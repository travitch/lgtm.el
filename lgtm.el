;;; lgtm.el --- Review changesets with Ediff -*- lexical-binding: t; -*-

;; Copyright (C) 2022-2023 Niklas Eklund
;; Copyright (C) 2026 Tristan Ravitch

;; Author: Tristan Ravitch <tristan@ravit.ch>, Niklas Eklund <niklas.eklund@posteo.net>
;; Maintainer: Tristan Ravitch <tristan@ravit.ch>
;; URL: https://github.com/travitch/lgtm.el
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (magit-section "4.3.5") (uuidgen "1.3"))
;; Keywords: convenience tools, code review, git

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides a magit-like `ediff' derived interface for reviewing changesets.

;;; Code:

;;;; Requirements

(require 'cl-lib)
(require 'ediff)
(require 'files)
(require 'magit-section)
(require 'seq)
(require 'subr-x)
(require 'uuidgen)

(require 'lgtm-core)

(cl-defstruct lgtm--file-comment-location
  (modified-file-state nil :read-only t :documentation "The mutable state of the comment (to update the selected index).")
  (location nil :read-only t :documentation "The location of the comment."))

(defun lgtm--make-new-comment-object (config comment-manager reply-to-id &optional file-comment-location)
  "Create a new empty comment in the COMMENT-MANAGER.
Returns the full mutable comment object, which also contains the
reference.  Takes the username from the CONFIG."
  (let* ((location (if file-comment-location (lgtm--file-comment-location-location file-comment-location) nil))
         (user (lgtm-configuration-user config))
         (ref (make-lgtm-comment-ref :id (uuidgen-4)))
         (comment (make-lgtm-comment :ref ref
                                     :location location
                                     :author user
                                     :reply-to-id reply-to-id
                                     :is-published nil
                                     :content ""))
         (tbl (lgtm--comment-manager-table comment-manager)))
    (puthash ref comment tbl)
    comment))

(defun lgtm--create-reply-comment (_config _comment-manager _comment)
  "Create a comment replying to COMMENT.

Adds necessary metadata in the COMMENT-MANAGER.  This requires a CONFIG
for the username."
  (error "Unimplemented: lgtm--create-reply-comment"))

;;;; Private

(defconst lgtm--comment-editor-buffer-name "*lgtm-comment*" "The name of the buffer that is used for editing comments.")
(defconst lgtm--overview-buffer-name "*lgtm*" "The name of the buffer that the overview UI is rendered in.")
(defvar lgtm--current-state nil "The mutable state of the current review.")

;;;; Functions

(defun lgtm-complete-comment ()
  "Complete the review comment.

Stores the new comment contents into the corresponding comment object and
then updates the UI."
  (interactive)
  (let* ((current-comment-ref (lgtm--state-comment-being-edited lgtm--current-state))
         (comment-manager (lgtm--state-comment-manager lgtm--current-state))
         (file-manager (lgtm--state-file-manager lgtm--current-state))
         (current-comment (lgtm--get-comment-content comment-manager current-comment-ref))
         (new-content (buffer-substring-no-properties (point-min) (point-max))))
    (setf (lgtm-comment-content current-comment) new-content)
    (setf (lgtm--state-comment-being-edited lgtm--current-state) nil)

    ;; FIXME:
    ;;
    ;; 1. Determine if this is a create or update of the comment (support update)
    ;;
    ;; 2. Handle top-level comments (non-file comments)

    ;; Send the comment to the server so that we can get its permanent server-side ID.  We need that
    ;; before we update the internal comment state.
    (let* ((config (lgtm--state-configuration lgtm--current-state))
           (create-comment-func (lgtm-configuration-create-review-comment-function config)))
      (if create-comment-func
          (lgtm--with-draft-review-id lgtm--current-state
                                            (lambda (review-id)
                                              (let ((comment-id (funcall create-comment-func review-id current-comment)))
                                                (setf (lgtm-comment-backend-data current-comment) comment-id))))
        (warn "No create comment function defined, not sending comment to server")))

    ;; Note: we only update overlays *if* this is a comment attached to a file. If this is a
    ;; top-level comment, there are no overlays to update.
    (when (lgtm-comment-location current-comment)
      (let* ((modified-file (lgtm--state-active-reviewed-file lgtm--current-state))
             (modified-file-state (lgtm--get-modified-file-state file-manager modified-file)))
        (lgtm--add-comment-to-file comment-manager modified-file-state current-comment-ref (lgtm-comment-location current-comment))
        (lgtm--init-comment-overlays lgtm--current-state modified-file))))

  (quit-restore-window (get-buffer-window lgtm--comment-editor-buffer-name) 'kill)
  (when (get-buffer-window lgtm--overview-buffer-name)
    (lgtm-redraw)))

(defun lgtm-quit-comment ()
  "Quit review comment.

Any changes to the current comment are discarded.  Any empty unpublished
comments are discarded."
  (interactive)
  (setf (lgtm--state-comment-being-edited lgtm--current-state) nil)
  (let* ((comment-manager (lgtm--state-comment-manager lgtm--current-state))
         (comment-table (lgtm--comment-manager-table comment-manager)))
    (maphash (lambda (comment-ref comment)
               (when (and (not (lgtm-comment-is-published comment)) (equal "" (lgtm-comment-content comment)))
                 (remhash comment-ref comment-table)))
             comment-table))

  (kill-buffer lgtm--comment-editor-buffer-name)
  (quit-restore-window
   (get-buffer-window (current-buffer))
   'kill))

(defun lgtm--insert-top-level-comment-summary (comment)
  "Insert a string summary of the COMMENT."
  (insert "Comment by " )
  (insert (propertize (lgtm-comment-author comment) 'font-lock-face 'bold))
  (insert " at " (lgtm--format-timestamp (lgtm-comment-created-timestamp comment)))
  (unless (equal (lgtm-comment-created-timestamp comment) (lgtm-comment-updated-timestamp comment))
    (insert " and updated at " (lgtm--format-timestamp (lgtm-comment-updated-timestamp comment)))))

(defun lgtm--insert-top-level-comment-body (comment)
  "Create a string representation of COMMENT."
  (lgtm--render-string-with-comment-mode (lgtm-comment-content comment)))

(defun lgtm--render-top-level-comment (comment)
  "Render a Magit section for a top-level COMMENT.
The IDX (index) is provided as context and can be used in formatting."
  (magit-insert-section (item comment t)
    (magit-insert-heading (lgtm--insert-top-level-comment-summary comment))
    (magit-insert-section-body
      (lgtm--insert-top-level-comment-body comment)
      (insert "\n\n"))))

(defun lgtm--repository-of-modified-file (modified-file)
  "Return the repository name of the MODIFIED-FILE."
  (lgtm-repository-name (lgtm--modified-file-repository modified-file)))

(defun lgtm--render-string-with-comment-mode (str &optional indent)
  "Render the STR into the current buffer.

This handles highlighting the text before inserting it and filling the
text to a reasonable width.  If provided, indent by INDENT spaces."
  (let* ((temp-buffer (generate-new-buffer "**lgtm-render-scratch**")))
    (with-current-buffer temp-buffer
      (when lgtm-comment-major-mode
        (funcall lgtm-comment-major-mode))

      (insert str)
      (fill-region (point-min) (point-max))
      (font-lock-ensure)
      (when indent
        (let ((indentation (string-pad "" indent (string-to-char " "))))
          (string-insert-rectangle (point-min) (point-max) indentation))))
    (insert-buffer-substring temp-buffer)
    (kill-buffer temp-buffer)))

(defun lgtm--render-highlighted-diff (str)
  "Render STR as a highlighted diff."
  (let* ((temp-buffer (generate-new-buffer "**lgtm-render-scratch**")))
    (with-current-buffer temp-buffer
      (diff-mode)
      (insert str)
      (font-lock-ensure))
    (insert-buffer-substring temp-buffer)
    (kill-buffer temp-buffer)))

(defun lgtm--render-review-overview-ui ()
  "The internal function to draw the main UI.

This function attempts to preserve the location of the point in cases
where the entire buffer is being redrawn."
  (with-current-buffer (get-buffer-create lgtm--overview-buffer-name)
    (lgtm-mode)
    (let ((inhibit-read-only t)
          (saved-point (point))
          (config (lgtm--state-configuration lgtm--current-state))
          (file-manager (lgtm--state-file-manager lgtm--current-state)))
      (erase-buffer)

      (magit-insert-section (magit-section "Overview")
        (magit-insert-heading (insert (propertize "Overview" 'font-lock-face '(:background "light gray")))
          (insert "\n")
          (insert "  " (propertize "Summary: " 'font-lock-face 'bold) (lgtm-configuration-changeset-title config) "\n")
          (insert "  " (propertize "State: " 'font-lock-face 'bold) (lgtm-configuration-state config) "\n")
          (insert "  " (propertize "Author: " 'font-lock-face 'bold) (lgtm-configuration-author config) "\n")
          (insert "  " (propertize "Created at " 'font-lock-face 'bold) (lgtm--format-timestamp (lgtm-configuration-created-at config)) "\n")
          (insert "  " (propertize "URL: " 'font-lock-face 'bold) (lgtm-configuration-changeset-url config))
          (insert "\n\n"))


        (magit-insert-section (list-section)
          (magit-insert-heading (insert (propertize "Description" 'font-lock-face '(:background "light gray"))))
          (let ((changeset-description (lgtm-configuration-changeset-description config)))
            (magit-insert-section-body
              (insert "\n")
              (lgtm--render-string-with-comment-mode changeset-description)
              (insert "\n\n")))))

      (magit-insert-section (list-section)
        (magit-insert-heading (insert (propertize "Modified Files" 'font-lock-face '(:background "light gray"))))

        (let ((grouped-files (seq-group-by #'lgtm--repository-of-modified-file (lgtm--modified-file-manager-modified-files file-manager))))
          (seq-doseq (group grouped-files)
            (let ((repo-name (car group))
                  (modified-files (cdr group)))

              (magit-insert-section (list-section)
                (magit-insert-heading (insert "  " (propertize repo-name 'font-lock-face 'bold)))

                (seq-doseq (modified-file modified-files)

                  (magit-insert-section (item modified-file t)
                    (magit-insert-heading (insert (lgtm--format-modified-file lgtm--current-state modified-file)))
                    (magit-insert-section-body
                      (lgtm--render-highlighted-diff (lgtm--format-modified-file-diff modified-file))
                      (insert "\n\n"))))))))

        (magit-insert-section-body (insert "\n\n")))

      (let* ((comment-manager (lgtm--state-comment-manager lgtm--current-state))
             (unpublished-comments (lgtm--top-level-unpublished-comments comment-manager))
             (unpublished-comment-count (length unpublished-comments)))

        (magit-insert-section (list-section)
          (if (= 0 unpublished-comment-count)
              (magit-insert-heading (insert "Top-level Comments"))
            (magit-insert-heading (insert (format "Top-level Comments (%d unpublished)" unpublished-comment-count))))

          (seq-doseq (comment (lgtm--top-level-comments comment-manager))
            (lgtm--render-top-level-comment comment))

          (magit-insert-section (comment-group nil t)
            (magit-insert-heading "Unpublished Comments")
            (seq-map-indexed #'lgtm--render-top-level-comment unpublished-comments))))

      (magit-insert-section (list-section)
        (magit-insert-heading (insert (propertize "Commits" 'font-lock-face '(:background "light gray"))))

        (let ((grouped-files (seq-group-by #'lgtm--modified-file-repository (lgtm--modified-file-manager-modified-files file-manager))))
          (seq-doseq (group grouped-files)
            (let ((repo (car group)))
              (magit-insert-section (list-section)
                (magit-insert-heading (insert "  " (propertize (lgtm-repository-name repo) 'font-lock-face 'bold)))
                (seq-doseq (commit (lgtm-repository-commits repo))
                  (magit-insert-section (item commit t)
                    (magit-insert-heading (insert (format "    %s   %s" (car commit) (cdr commit)))))))))))

      (goto-char saved-point))

    (pop-to-buffer (current-buffer))))

(defun lgtm-redraw ()
  "Re-render the top-level UI."
  (interactive)
  (lgtm--render-review-overview-ui))

(defun lgtm--populate-file-contents-at-revision (repository revision file)
  "Populate the current buffer with file contents from git.

The BUFFER is populated with the contents of the given FILE at the given
REVISION from git REPOSITORY."
  (let* ((default-directory (lgtm-repository-path repository))
         (git-command (format "git show '%s:%s'" revision file)))
      ;; Pipes the output from git into the current buffer
      (call-process-shell-command git-command nil t)))

(defun lgtm--enable-mode (base-buffer current-buffer)
  "Deduce the mode for the BASE-BUFFER based on the CURRENT-BUFFER."
  (with-current-buffer base-buffer
    (when (eq major-mode 'fundamental-mode)
      (funcall
       (with-current-buffer current-buffer major-mode)))))

(defun lgtm--setup-review-buffers (state modified-file)
  "Create the old/new file buffers for MODIFIED-FILE, storing in STATE."
  (let* ((repository (lgtm--modified-file-repository modified-file))
         (repository-path (lgtm-repository-path repository))
         (current-revision-file-name (lgtm--modified-file-current-filename modified-file))
         (current-revision-file-path (format "%s/%s" repository-path current-revision-file-name))
         (current-revision-buffer (find-file-noselect current-revision-file-path))
         ;; Note: when the file has the same name between revisions (i.e., without a rename or copy), the original filename is nil
         (base-revision-file-name (or (lgtm--modified-file-base-filename modified-file) current-revision-file-name))
         (base-revision-buffer-name (format "<base>%s" (file-name-nondirectory base-revision-file-name)))
         (base-revision-buffer (get-buffer-create base-revision-buffer-name)))

    ;; Save these buffers so that we can clean them up later
    (push base-revision-buffer (lgtm--state-review-file-buffers state))
    (push current-revision-buffer (lgtm--state-review-file-buffers state))

    (with-current-buffer current-revision-buffer
      (read-only-mode)
      (lgtm-minor-mode))

    (with-current-buffer base-revision-buffer
      (let ((inhibit-read-only t))
        (erase-buffer)
        (unless (eq 'added (lgtm--modified-file-type modified-file))
          (let ((base-revision (lgtm-repository-base-revision (lgtm--modified-file-repository modified-file))))
            (lgtm--populate-file-contents-at-revision repository base-revision base-revision-file-name))))
      (read-only-mode))

    (setf (lgtm--state-base-revision-buffer state) base-revision-buffer)
    (setf (lgtm--state-current-revision-buffer state) current-revision-buffer)

    (lgtm--enable-mode base-revision-buffer current-revision-buffer)
    (with-current-buffer base-revision-buffer
      (lgtm-minor-mode))))

;; Public

(defun lgtm-close-review-file ()
  "Close down the ediff UI for any active file review.

This jumps to the control pane first, as quitting ediff outside
of the control pane fails."
  (interactive)
  (lgtm-jump-to-ediff-control-pane)
  (cl-letf (((symbol-function #'y-or-n-p) (lambda (&rest _args) t)))
    (call-interactively #'ediff-quit))

  (setf (lgtm--state-active-reviewed-file lgtm--current-state) nil)

  ;; Try our best to incrementally clean up buffers
  ;;
  ;; See [ref:buffer-cleanup]
  (kill-buffer (lgtm--state-base-revision-buffer lgtm--current-state))
  (kill-buffer (lgtm--state-current-revision-buffer lgtm--current-state))

  ;; Restore the window configuration from before `ediff-buffers' ran.
  ;;
  ;; See [ref:ediff-window-save-register]
  (jump-to-register ?±)

  ;; Return to the top-level UI
  (lgtm--render-review-overview-ui))


(defun lgtm-submit-comments ()
  "Submit local comments to the server.

After local comments are successfully submitted, they are deleted
from the local cache."
  (interactive)
  (let* ((conf (lgtm--state-configuration lgtm--current-state))
         (submit-review-function (lgtm-configuration-submit-review-function conf)))
    (if (and submit-review-function (y-or-n-p "Publish review comments?"))
        (lgtm--with-draft-review-id lgtm--current-state
                                    (lambda (review-id)
                                      (let ((error-result (funcall submit-review-function review-id)))
                                        (when error-result
                                          (error "Failed to submit review: `%s'" error-result)))))
      (warn "No function is defined to submit the review"))))

(defun lgtm--edit-comment (state comment-ref)
  "Open the comment editor for the current comment in STATE.

This updates the state to mark the given COMMENT-REF as the current comment.
Doing so here ensures that no call can forget to update the current comment."
  (setf (lgtm--state-comment-being-edited state) comment-ref)
  (let* ((comment-manager (lgtm--state-comment-manager state))
         (current-comment-ref (lgtm--state-comment-being-edited state))
         (current-comment (lgtm--get-comment-content comment-manager current-comment-ref))
         (buffer (get-buffer-create lgtm--comment-editor-buffer-name)))
    (display-buffer buffer lgtm-comment-buffer-action)
    (with-current-buffer buffer
      (erase-buffer)
      (insert (lgtm-comment-content current-comment))
      (when lgtm-comment-major-mode
        (funcall lgtm-comment-major-mode))

      (run-mode-hooks 'lgtm-comment-mode-hook)

      (lgtm-comment-mode)
      (select-window (get-buffer-window (current-buffer)))
      (goto-char (point-max)))))

(defun lgtm-add-top-level-comment ()
  "Add a top-level comment to the review.

Top-level comments are associated with the review and not a range of code."
  (interactive)
  ;; Create a comment object with a new UUID
  (let* ((config (lgtm--state-configuration lgtm--current-state))
         (comment-manager (lgtm--state-comment-manager lgtm--current-state))
         (comment (lgtm--make-new-comment-object config comment-manager nil))
         (ref (lgtm-comment-ref comment)))
    (lgtm--comment-manager-add-top-level comment-manager ref)
    (lgtm--edit-comment lgtm--current-state ref)))

(defun lgtm-mark-selected-modified-file-reviewed ()
  "Mark the modified file selected in the UI as having been reviewed.

Note that opening a modified file in the review UI does not automatically mark
it as reviewed; explicit marking is required to change the state.  Files do not
need to be explicitly marked as reviewed to submit a review."
  (interactive)
  (let* ((selected-section (magit-section-at))
         (modified-file (magit-section-ident-value selected-section))
         (conf (lgtm--state-configuration lgtm--current-state)))
    (funcall (lgtm--file-review-state-backend-mark-reviewed (lgtm-configuration-review-state-backend conf)) modified-file)
    (let* ((selected-section (magit-section-at))
           (section-start-pos (marker-position (slot-value selected-section 'start))))
      (magit-section-hide selected-section)
      (lgtm--render-review-overview-ui)
      (goto-char section-start-pos))))

(defun lgtm-mark-selected-modified-file-unreviewed ()
  "Mark the modified file selected in the UI as having not been reviewed."
  (interactive)
  (let* ((selected-section (magit-section-at))
         (modified-file (magit-section-ident-value selected-section))
         (conf (lgtm--state-configuration lgtm--current-state)))
    (funcall (lgtm--file-review-state-backend-mark-unreviewed (lgtm-configuration-review-state-backend conf)) modified-file)
    (lgtm--render-review-overview-ui)))

(defun lgtm--ediff-control-window ()
  "Return the window for the ediff control buffer."
  (seq-find (lambda (it)
              (with-selected-window it ediff-control-buffer))
            (window-list)))

(defun lgtm-next-hunk ()
  "Go to the next hunk."
  (interactive)
  (ediff-next-difference))

(defun lgtm-previous-hunk ()
  "Go to the previous hunk."
  (interactive)
  (ediff-previous-difference))

(defun lgtm--restore-saved-buffer-locations (state modified-file)
  "Restore any saved buffer locations in the ediff view.

If the saved locations for the current MODIFIED-FILE from the STATE are non-nil,
set them as the current states."
  (let* ((file-manager (lgtm--state-file-manager state))
         (modified-file-state (lgtm--get-modified-file-state file-manager modified-file))
         (base-revision-buffer (lgtm--state-base-revision-buffer state))
         (current-revision-buffer (lgtm--state-current-revision-buffer state))
         (current-file-location (lgtm--modified-file-state-current-file-location modified-file-state))
         (base-file-location (lgtm--modified-file-state-base-file-location modified-file-state)))
    (if (or current-file-location base-file-location)
        (progn
          (when current-file-location
            (with-selected-window (get-buffer-window current-revision-buffer)
              (goto-char current-file-location)))

          (with-selected-window (lgtm--ediff-control-window)
            (let ((last-command-event ?b))
              (ediff-jump-to-difference-at-point nil)))

          (when current-file-location
            (with-selected-window (get-buffer-window current-revision-buffer)
              (goto-char current-file-location)))

          (when base-file-location
            (with-selected-window (get-buffer-window base-revision-buffer)
              (goto-char base-file-location))))
      (with-selected-window (lgtm--ediff-control-window)
        (lgtm-next-hunk)))))

(defun lgtm--get-comment-overlays (comment)
  "Return all of the overlays associated with COMMENT."
  (let ((comment-id (lgtm-comment-ref comment)))
    (when-let* ((buffer-overlays (overlays-in (point-min) (point-max))))
      (seq-filter (lambda (overlay)
                    (equal (overlay-get overlay 'lgtm-comment-id)
                            comment-id))
                  buffer-overlays))))

(defun lgtm--get-comment-region-overlay (buffer comment)
  "Return the region overlay for COMMENT.

If there is an existing overlay for the comment, return it.  Otherwise
create a new one.  The region is computed with respect to BUFFER."
  (with-current-buffer buffer
    (or (seq-find (lambda (it) (eq 'region (overlay-get it 'lgtm-overlay-type)))
                  (lgtm--get-comment-overlays comment))
        (make-overlay (lgtm--comment-start-point buffer comment)
                      (lgtm--comment-end-point buffer comment)))))

(defun lgtm--get-comment-header-overlay (buffer comment)
  "Return the header overlay for COMMENT.

This returns an existing header overlay or creates a new one if
none exists.  It is computed with respect to BUFFER."
  (with-current-buffer buffer
    (save-excursion
      (goto-char (point-min))
      (let ((loc (lgtm-comment-location comment)))
        (forward-line (lgtm-comment-location-start-line loc))
        (beginning-of-line)
        (or (seq-find (lambda (it) (eq 'header (overlay-get it 'lgtm-overlay-type)))
                      (lgtm--get-comment-overlays comment))
            (make-overlay (point) (point)))))))

(defun lgtm--format-timestamp (timestamp)
  "Format TIMESTAMP as a string according to the configured format."
  (format-time-string lgtm-timestamp-format timestamp))

(defun lgtm--add-comment-overlays (buffer selected-index idx depth comment)
  "Add overlays for the given COMMENT in the currently-viewed file BUFFER.

The IDX is the index of the comment.  The SELECTED-INDEX is the highlighted
comment, if any.  Indent the comment according to DEPTH, which encodes the
reply structure.

Accepts a COMMENT-MANAGER to retrieve the rest of the thread.
The STATE is required to get the buffer to host the overlays.
Note that comments are always against the current revision."

    ;; Install the region overlay
    (let ((ov (lgtm--get-comment-region-overlay buffer comment)))
      (overlay-put ov 'lgtm-comment-id (lgtm-comment-ref comment))
      (overlay-put ov 'lgtm-overlay-type 'region)
      (overlay-put ov 'face 'ansi-color-fast-blink))

    ;; Install the header overlay
    (let* ((ov (lgtm--get-comment-header-overlay buffer comment))
           (timestamp (lgtm-comment-created-timestamp comment))
           (time-str (if timestamp (lgtm--format-timestamp timestamp) ""))
           (user (lgtm-comment-author comment))
           (is-published (lgtm-comment-is-published comment))
           (content (lgtm-comment-content comment))
           (header-content (concat "| " user " at " time-str (if (not is-published) " [DRAFT]") " |" "\n\n" content "\n"))
           (comment-face (if (eq selected-index idx) 'lgtm-selected-comment-face 'lgtm-default-comment-face)))
      (overlay-put ov 'lgtm-comment-id (lgtm-comment-ref comment))
      (overlay-put ov 'lgtm-overlay-type 'header)
      (with-temp-buffer
        (lgtm--render-string-with-comment-mode header-content (* 4 depth))
        (insert "\n")
        (overlay-put ov 'before-string (propertize (buffer-substring (point-min) (point-max)) 'face comment-face)))))

(defun lgtm--init-comment-overlays (state modified-file)
  "Initialize comment overlays for the given MODIFIED-FILE file.

This requires STATE to get the buffer to add overlays to."
  (let* ((file-manager (lgtm--state-file-manager state))
         (comment-manager (lgtm--state-comment-manager state))
         (modified-file-state (lgtm--get-modified-file-state file-manager modified-file))
         (base-buffer (lgtm--state-base-revision-buffer state))
         (base-selected-comment (lgtm--modified-file-state-base-selected-conversation-index modified-file-state))
         (base-comments (lgtm--modified-file-state-base-conversations modified-file-state))
         (positioned-base-comments (lgtm--index-comments-by-ref comment-manager modified-file 'base base-comments))
         (current-buffer (lgtm--state-current-revision-buffer state))
         (current-selected-comment (lgtm--modified-file-state-current-selected-conversation-index modified-file-state))
         (current-comments (lgtm--modified-file-state-current-conversations modified-file-state))
         (positioned-current-comments (lgtm--index-comments-by-ref comment-manager modified-file 'current current-comments)))

    (seq-map (lambda (positioned-comment)
               (let ((idx (lgtm--positioned-comment-index positioned-comment))
                     (depth (lgtm--positioned-comment-indent positioned-comment))
                     (comment (lgtm--positioned-comment-comment positioned-comment)))
                 (lgtm--add-comment-overlays base-buffer base-selected-comment idx depth comment)))
             (lgtm--get-positioned-comments positioned-base-comments))

    (seq-map (lambda (positioned-comment)
               (let ((idx (lgtm--positioned-comment-index positioned-comment))
                     (depth (lgtm--positioned-comment-indent positioned-comment))
                     (comment (lgtm--positioned-comment-comment positioned-comment)))
                 (lgtm--add-comment-overlays current-buffer current-selected-comment idx depth comment)))
             (lgtm--get-positioned-comments positioned-current-comments))))

(defun lgtm--initialize-ediff-view (state modified-file)
  "Initialize the ediff view.

This reads the STATE and MODIFIED-FILE to set up ediff windows."
  ;; Save the window configuration into a register so that we can restore it later.
  ;; The register is a difficult to type character so that it is extremely unlikely
  ;; to collide with registers that a user would use themselves.
  ;;
  ;; [tag:ediff-window-save-register]
  (window-configuration-to-register ?±)
  (cl-letf* (((symbol-function #'ediff-set-keys) #'ignore)
             (base-revision-buffer (lgtm--state-base-revision-buffer state))
             (current-revision-buffer (lgtm--state-current-revision-buffer state)))
    (setf (lgtm--state-active-reviewed-file state) modified-file)
    (ediff-buffers base-revision-buffer current-revision-buffer)

    ;; Set bindings for the ediff control pane
    (with-selected-window (lgtm--ediff-control-window)
      (lgtm-ediff-mode))

    (lgtm--init-comment-overlays state modified-file)
    (lgtm--restore-saved-buffer-locations state modified-file)))

(defun lgtm--modify-base-selected-comment (modified-file-state func)
  "Apply FUNC to the selected base conversation index in the MODIFIED-FILE-STATE.

The FUNC is called as (funcall func current-index total-comments)."
  (let* ((selected-base-index (lgtm--modified-file-state-base-selected-conversation-index modified-file-state))
         (base-conversations (lgtm--modified-file-state-base-conversations modified-file-state))
         (comment-count (length base-conversations))
         (next-index (funcall func selected-base-index comment-count)))
    (setf (lgtm--modified-file-state-base-selected-conversation-index modified-file-state) next-index)))

(defun lgtm--modify-current-selected-comment (modified-file-state func)
  "Apply FUNC to the selected current conversation index.

This updates the MODIFIED-FILE-STATE.

The FUNC is called as (funcall func current-index total-comments)."
  (let* ((selected-current-index (lgtm--modified-file-state-current-selected-conversation-index modified-file-state))
         (current-conversations (lgtm--modified-file-state-current-conversations modified-file-state))
         (comment-count (length current-conversations))
         (next-index (funcall func selected-current-index comment-count)))
    (setf (lgtm--modified-file-state-current-selected-conversation-index modified-file-state) next-index)))


(defun lgtm-select-next-comment ()
  "Select the next comment in the current file version being reviewed."
  (interactive)
  (let ((active-reviewed-file (lgtm--state-active-reviewed-file lgtm--current-state)))
    (when active-reviewed-file
      (let* ((file-manager (lgtm--state-file-manager lgtm--current-state))
             (active-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file))
             (index-transformer (lambda (current-index comment-count) (if current-index (min (- comment-count 1) (+ 1 current-index)) 0))))
        (pcase (lgtm--get-selected-buffer-tag lgtm--current-state)
          ('base (lgtm--modify-base-selected-comment active-file-state index-transformer))
          ('current (lgtm--modify-current-selected-comment active-file-state index-transformer))
          (_ (error "Either the base or current buffer must be selected")))
        (lgtm--init-comment-overlays lgtm--current-state active-reviewed-file)))))

(defun lgtm-select-previous-comment ()
  "Select the previous comment in the current file version being reviewed."
  (interactive)
  (let ((active-reviewed-file (lgtm--state-active-reviewed-file lgtm--current-state)))
    (when active-reviewed-file
      (let* ((file-manager (lgtm--state-file-manager lgtm--current-state))
             (active-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file))
             (index-transformer (lambda (current-index _comment-count) (if current-index (max 0 (- current-index 1)) nil))))
        (pcase (lgtm--get-selected-buffer-tag lgtm--current-state)
          ('base (lgtm--modify-base-selected-comment active-file-state index-transformer))
          ('current (lgtm--modify-current-selected-comment active-file-state index-transformer))
          (_ (error "Either the base or current buffer must be selected")))
        (lgtm--init-comment-overlays lgtm--current-state active-reviewed-file)))))

(defun lgtm-clear-selected-comment ()
  "Deselect the currently selected comment in the current review buffer."
  (interactive)
  (let ((active-reviewed-file (lgtm--state-active-reviewed-file lgtm--current-state)))
    (when active-reviewed-file
      (let* ((file-manager (lgtm--state-file-manager lgtm--current-state))
             (active-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file))
             (index-transformer (lambda (_current-index _comment-count) nil)))
        (pcase (lgtm--get-selected-buffer-tag lgtm--current-state)
          ('base (lgtm--modify-base-selected-comment active-file-state index-transformer))
          ('current (lgtm--modify-current-selected-comment active-file-state index-transformer))
          (_ (error "Either the base or current buffer must be selected"))))
      (lgtm--init-comment-overlays lgtm--current-state active-reviewed-file))))

(defun lgtm-clear-selected-comments ()
  "Deselect all selected comments (in both review buffers)."
  (interactive)
  (let ((active-reviewed-file (lgtm--state-active-reviewed-file lgtm--current-state)))
    (when active-reviewed-file
      (let* ((file-manager (lgtm--state-file-manager lgtm--current-state))
             (active-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file)))
        (setf (lgtm--modified-file-state-base-selected-conversation-index active-file-state) nil)
        (setf (lgtm--modified-file-state-current-selected-conversation-index active-file-state) nil))
      (lgtm--init-comment-overlays lgtm--current-state active-reviewed-file))))

(defun lgtm-review-selected-modified-file ()
  "Show the review UI for the modified file selected in the overview UI."
  (interactive)
  (let* ((selected-section (magit-section-at))
         (modified-file (magit-section-ident-value selected-section)))
    (lgtm--setup-review-buffers lgtm--current-state modified-file)
    (lgtm--initialize-ediff-view lgtm--current-state modified-file)))

(defun lgtm-reply-to-selected-comment ()
  "Create a reply to the selected comment, if any."
  (interactive)
  (when-let ((active-reviewed-file (lgtm--state-active-reviewed-file lgtm--current-state)))
    (let* ((file-manager (lgtm--state-file-manager lgtm--current-state))
           (active-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file))
           (comment-manager (lgtm--state-comment-manager lgtm--current-state))
           (parent-comment-ref (pcase (lgtm--get-selected-buffer-tag lgtm--current-state)
                                 ('base (let ((selected-idx (lgtm--modified-file-state-base-selected-conversation-index active-file-state)))
                                          (elt (lgtm--modified-file-state-base-conversations active-file-state) selected-idx)))
                                 ('current (let ((selected-idx (lgtm--modified-file-state-current-selected-conversation-index active-file-state)))
                                             (elt (lgtm--modified-file-state-current-conversations active-file-state) selected-idx)))
                                 (_ (error "Either the base or current buffer must be selected"))))
           (parent-comment (lgtm--get-comment-content comment-manager parent-comment-ref))
           (reply-to-id (lgtm-comment-reply-to-id parent-comment))
           (config (lgtm--state-configuration lgtm--current-state))
           (loc (lgtm-comment-location parent-comment))
           (file-comment-location (make-lgtm--file-comment-location :modified-file-state active-file-state
                                                                    :location loc))
           (reply-comment (lgtm--make-new-comment-object config comment-manager reply-to-id file-comment-location)))

      (lgtm--edit-comment lgtm--current-state (lgtm-comment-ref reply-comment)))))

(defun lgtm--create-comment-at-point (state)
  "Create a new comment at the point based on STATE."
  (let* ((config (lgtm--state-configuration state))
         (comment-manager (lgtm--state-comment-manager state))
         (file-manager (lgtm--state-file-manager state))
         (active-reviewed-file (lgtm--state-active-reviewed-file state))
         (active-reviewed-file-state (lgtm--get-modified-file-state file-manager active-reviewed-file))
         (selected-buffer-tag (lgtm--get-selected-buffer-tag state)))
    (cl-assert (not (eq nil selected-buffer-tag)) t "This function must be called in the context of an active review.")
    (let* ((loc (lgtm-comment-location-at-point active-reviewed-file selected-buffer-tag))
           (file-comment-location (make-lgtm--file-comment-location :modified-file-state active-reviewed-file-state
                                                                    :location loc)))
      (lgtm--make-new-comment-object config comment-manager nil file-comment-location))))

(defun lgtm-conversation-dwim ()
  "Create or edit a comment in the review UI.

If the comment is new/draft, edit it.  Otherwise, create a reply and edit it."
  (interactive)
  (let ((config (lgtm--state-configuration lgtm--current-state))
        (comment-manager (lgtm--state-comment-manager lgtm--current-state))
        (comment (lgtm--create-comment-at-point lgtm--current-state)))
    ;; After we get the location, clear the mark in case the user had highlighted a region to
    ;; comment on
    (deactivate-mark)
    (if (lgtm-comment-is-published comment)
        (let ((reply-comment (lgtm--create-reply-comment config comment-manager comment)))
          (lgtm--edit-comment lgtm--current-state (lgtm-comment-ref reply-comment)))
      (lgtm--edit-comment lgtm--current-state (lgtm-comment-ref comment)))))

(defun lgtm-jump-to-ediff-control-pane ()
  "From the ediff review panes, jump back to the control pane."
  (interactive)
  (select-window (lgtm--ediff-control-window)))

(defun lgtm-approve ()
  "Approve the review.

This uses the approval function from the configuration, if defined,
to submit the approval to the server."
  (interactive)
  (let* ((conf (lgtm--state-configuration lgtm--current-state))
         (approve-function (lgtm-configuration-approve-review-function conf)))
    (message "Approving review")
    (if (and approve-function (y-or-n-p "Approve change?"))
        (funcall approve-function lgtm--current-state)
      (warn "No review approval function is defined"))))

(defun lgtm-shutdown ()
  "Shut down the LGTM session."
  (interactive)
  (let* ((conf (lgtm--state-configuration lgtm--current-state))
         (shutdown-hook (lgtm-configuration-shutdown-hook conf)))
    (when shutdown-hook
      (funcall shutdown-hook))

    ;; Clean up any file review buffers that were not already killed
    ;;
    ;; See [ref:buffer-cleanup].
    (seq-doseq (buffer (lgtm--state-review-file-buffers lgtm--current-state))
      (kill-buffer buffer))

    (kill-buffer (get-buffer lgtm--overview-buffer-name))))


(defun lgtm-start (conf)
  "Review the given changeset.

The backend-specific entrypoint is expected to pass in the necessary CONF."
  (seq-doseq (repository (lgtm-configuration-repositories conf))
    (cl-assert (file-name-absolute-p (lgtm-repository-path repository)) t "All repository paths must be absolute"))

  (when lgtm--current-state
    (message "Cleaning up the previous lgtm session")
    (lgtm-shutdown))

  (message "Start review")

  (let* ((get-remote-conversations (lgtm-configuration-get-remote-conversations-function conf))
         (modified-files (lgtm--compute-modified-files (lgtm-configuration-repositories conf)))
         (file-manager (lgtm--make-modified-file-manager modified-files))
         (remote-conversations (if get-remote-conversations (funcall get-remote-conversations file-manager) '()))
         (state (make-lgtm--state
                 :configuration conf
                 :file-manager file-manager)))

    (lgtm--add-remote-comments file-manager (lgtm--state-comment-manager state) remote-conversations)

    (setq lgtm--current-state state)
    (lgtm--render-review-overview-ui)))

;; Mode definitions

;; This is the keymap for the top-level changeset view
(defvar lgtm-mode-map
  (let ((map (make-sparse-keymap)))

    (set-keymap-parent map magit-section-mode-map)

    (define-key map (kbd "RET") #'lgtm-review-selected-modified-file)
    (define-key map (kbd "R") #'lgtm-mark-selected-modified-file-reviewed)
    (define-key map (kbd "U") #'lgtm-mark-selected-modified-file-unreviewed)
    (define-key map (kbd "A") #'lgtm-approve)
    (define-key map (kbd "C") #'lgtm-add-top-level-comment)
    (define-key map (kbd "S") #'lgtm-submit-comments)
    (define-key map (kbd "q") #'lgtm-shutdown)

    map))

;; Ideally this would derive from magit-section-mode.  That did not work for lgtm because
;; magit-section-mode installs a filter that removes properties from text inserted into the
;; magit-section buffer.  That breaks some highlighting that lgtm wants to insert.
;;
;; Instead, lgtm-mode extends the magit-section-mode keymap and ports over the setup steps
;; from magit-section-mode that do work for lgtm.
(define-derived-mode lgtm-mode fundamental-mode "LGTM"
  "Major mode for performing code reviews."

  (buffer-disable-undo)
  (setq buffer-read-only t)
  (setq-local line-move-visual t)
  (setq show-trailing-whitespace nil)
  (setq-local symbol-overlay-inhibit-map t)

  (add-hook 'pre-command-hook #'magit-section-pre-command-hook nil t)
  (add-hook 'post-command-hook #'magit-section-post-command-hook t t)
  (add-hook 'deactivate-mark-hook #'magit-section-deactivate-mark t t)

  (setq-local redisplay-highlight-region-function
              #'magit-section--highlight-region)
  (setq-local redisplay-unhighlight-region-function
              #'magit-section--unhighlight-region)

  (when (fboundp 'magit-section-context-menu)
    (add-hook 'context-menu-functions #'magit-section-context-menu 10 t))
  (when magit-section-disable-line-numbers
    (when (and (fboundp 'linum-mode)
               (bound-and-true-p global-linum-mode))
      (linum-mode -1))
    (when (and (fboundp 'nlinum-mode)
               (bound-and-true-p global-nlinum-mode))
      (nlinum-mode -1))
    (when (and (fboundp 'display-line-numbers-mode)
               (bound-and-true-p global-display-line-numbers-mode))
      (display-line-numbers-mode -1)))
  (when (fboundp 'magit-preserve-section-visibility-cache)
    (add-hook 'kill-buffer-hook #'magit-preserve-section-visibility-cache)))

;; This is the keymap used for the ediff control pane.
;;
;; These are useful keybindings in addition to the defaults provided by the ediff control pane.
;; This set of commands has some overlap with the `lgtm-minor-mode' used in the source buffers.
(defvar lgtm-ediff-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "q") #'lgtm-close-review-file)
    (define-key map (kbd "n") #'lgtm-next-hunk)
    (define-key map (kbd "p") #'lgtm-previous-hunk)
    (define-key map (kbd "M-n") #'lgtm-select-next-comment)
    (define-key map (kbd "M-p") #'lgtm-select-previous-comment)
    (define-key map (kbd "R") #'lgtm-reply-to-selected-comment)
    (define-key map (kbd "0") #'lgtm-clear-selected-comment)
    (define-key map (kbd "v") #'ediff-scroll-vertically)
    (define-key map (kbd "V") #'ediff-scroll-vertically)

    map))

(define-derived-mode lgtm-ediff-mode ediff-mode "LGTM-Ediff"
  "Major mode for the lgtm ediff control pane.")

(define-minor-mode lgtm-comment-mode
  "Mode for editing comments in `lgtm'."
  :global nil
  :lighter " LGTM Comment"
  :keymap (let ((map (make-sparse-keymap)))
            (define-key map (kbd "C-c C-c") #'lgtm-complete-comment)
            (define-key map (kbd "C-c C-k") #'lgtm-quit-comment)
            map))

(define-minor-mode lgtm-minor-mode
  "The minor mode for `lgtm' ediff code buffers.
This is active in the ediff UI to trigger review actions."
  :global nil
  :lighter "LGTM"
  :keymap (let ((map (make-sparse-keymap)))
            (define-key map (kbd "C-c C-c") #'lgtm-jump-to-ediff-control-pane)
            (define-key map (kbd "q") #'lgtm-close-review-file)
            (define-key map (kbd "C") #'lgtm-conversation-dwim)
            (define-key map (kbd "M-n") #'lgtm-select-next-comment)
            (define-key map (kbd "M-p") #'lgtm-select-previous-comment)
            (define-key map (kbd "R") #'lgtm-reply-to-selected-comment)
            (define-key map (kbd "0") #'lgtm-clear-selected-comment)
            (define-key map (kbd "n") #'lgtm-next-hunk)
            (define-key map (kbd "p") #'lgtm-previous-hunk)

            map))

(provide 'lgtm)

;;; lgtm.el ends here
