;;; lgtm-core.el --- Review changesets with Ediff core functions -*- lexical-binding: t; -*-

;; Copyright (C) 2022-2023 Niklas Eklund
;; Copyright (C) 2026 Tristan Ravitch

;; Author: Tristan Ravitch <tristan@ravit.ch>, Niklas Eklund <niklas.eklund@posteo.net>
;; Maintainer: Tristan Ravitch <tristan@ravit.ch>
;; URL: https://github.com/travitch/lgtm.el
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (magit-section "4.3.5") (uuidgen "1.3"))
;; Keywords: convenience tools, git, code review

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

;; These are core functions with no external dependencies that are fairly easy to test.

;;; Code:

;;; Requirements
(require 'cl-lib)
(require 'ediff)
(require 'files)
(require 'seq)
(require 'subr-x)

;;; Variables


;;; Customizable

(defcustom lgtm-comment-mode-hook nil
  "A list of hooks invoked when the comment mode is entered.

These hooks are invoked after the major mode is applied."
  :type 'hook
  :tag "lgtm-comment-mode-hook"
  :group 'lgtm)

(defcustom lgtm-comment-major-mode #'text-mode
  "Defines the major mode to use for composing comments.

This configuration is separate from the comment hook because the comment
major mode is also used to syntax highlight comments rendered in the UI.
Rendering those comments does not run the hook."
  :type 'symbol
  :group 'lgtm)

(defcustom lgtm-database-file (locate-user-emacs-file "lgtm.sqlite")
  "The SQLite database for modified file review statuses.

Set this to nil to disable storing file review statuses."
  :type 'string
  :group 'lgtm)

(defcustom lgtm-timestamp-format "%F %T"
  "The format string to use to format timestamps in the UI."
  :type 'string
  :group 'lgtm)

(defcustom lgtm-comment-buffer-action
  '(display-buffer-in-side-window
    (side . bottom)
    (slot . -1))
  "The action used to display a comment."
  :group 'lgtm
  :type 'sexp)

;;; Faces

(defface lgtm-default-comment-face
  '((t :extend t :background "powder blue"))
  "Face used to highlight comments that are not selected.")

(defface lgtm-selected-comment-face
  '((t :extend t :background "light goldenrod"))
  "Face used to highlight comments that are selected.")

;;; Type Definitions

(cl-defstruct lgtm--modified-file-state
  (ref nil :read-only t :documentation "The immutable reference that points to this state.")
  (base-file-location nil :documentation "The saved cursor position in the old/original file")
  (current-file-location nil :documentation "The saved cursor position in the current file")
  (base-selected-conversation-index nil :documentation "The index into the comments list for the base file that is selected.
This field is nil for no selection.")
  (current-selected-conversation-index nil :documentation "The index into the comments list for the current file that is selected.
This field is nil for no selection.")
  (base-conversations '() :documentation "The conversations in the base version of the file.

This is a list of `lgtm-comment-ref' stored in structural order.  The structural
order is such that a linear traversal respects thread order and nesting.")
  (current-conversations '() :documentation "The conversations in the current version of the file.

This is a list of `lgtm-comment-ref' stored in structural order.  The structural
order is such that a linear traversal respects thread order and nesting."))

(defun lgtm--path-of-file-at-version (version modified-file)
  "Get the path of the VERSION of the MODIFIED-FILE.

This is an interesting helper because the path is nil for the base file if
it is the same as the current file."
  (pcase version
    ('current (lgtm--modified-file-current-filename modified-file))
    ('base (let ((base-filename (lgtm--modified-file-base-filename modified-file)))
             (if base-filename
                 base-filename
               (lgtm--modified-file-current-filename modified-file))))
    (_ (error "Invalid version for file %s" modified-file))))

;;; * Repositories

;; The type of repositories comprising a changeset.
;;
;; A repository is required to already exist on disk. Each repository is simply a path to a git
;; repository.
(cl-defstruct lgtm-repository
  (base-revision nil :read-only t :documentation "The base revision commit hash to compare HEAD against.")
  (name nil :read-only t :documentation "A human readable name for the repository.

This is used in the UI.")
  (commits nil :read-only t :documentation "The list of commits and their commit messages for
the change in this repository.

This is an alist where keys are commit hashes and the values are commit
messages.")
  (path nil :read-only t :documentation "The path to the repository on disk"))

;;; * Configurations

;; The type of configuration objects.
;;
;; The lgtm-config, which can be overridden by users, returns one of these. The library treats
;; changeset-id as opaque; callers can pass in structured data that they then pass to the
;; submit-review-function and the get-remote-conversations-function.
;;
;; The core concept is that users can use any logic they want to create a changeset id. For example, users
;; could inspect metadata in the git repository to get a PR number and/or link and use that as the id.
(cl-defstruct lgtm-configuration
  (user nil :read-only t :documentation "The username associated with the review.")
  (changeset-id nil :read-only t :documentation "The identifier for the changeset.
This is included so that it can be passed to the review submission process.
It is opaque to this library.")
  (repositories '() :read-only t :documentation "A list of repositories containing code relevant to the changeset.")
  (author nil :read-only t :documentation "The author of the changeset.")
  (changeset-url nil :read-only t :documentation "A URL to view the changeset online.")
  (created-at nil :read-only t :documentation "The time at which the changeset was created.")
  (state nil :read-only t :documentation "The state of the changeset (e.g., open, closed, merged).")
  (changeset-title nil :read-only t :documentation "The title of the changeset.")
  (changeset-description nil :read-only t :documentation "The description of the changeset.")

  (review-state-backend nil :read-only t :documentation "The backend used to store the reviewed state of modified files.

Each file in a changeset can be reviewed or unreviewed.  This storage
backend persists that state across review sessions, if enabled.")
  (get-remote-conversations-function nil :read-only t :documentation "A function called with the configuration object
and file manager that fetches any remote conversations attached to the review.

Called with a single argument, the file manager, which is used to associate
conversations with files.")
  (create-review-comment-function nil :read-only t :documentation "A function to create a draft comment in
the current active review.

This package ensures that a review exists before calling this function.
This function is called with the review id and the comment object.
If the location is nil, the comment is
a top-level comment on the review as a whole.

Called with the comment to create.

This function should return the identifier of the comment.")
  (update-review-comment-function nil :read-only t :documentation "Update the content of a review comment.")
  (delete-review-comment-function nil :read-only t :documentation "Delete a draft review comment.

This is called with the review id and the comment id.  This will fail if the
comment is already published.")
  (submit-review-function nil :read-only t :documentation "A function to submit the draft review to
the server.  It is called with no arguments.

Returns `nil' on success.  Otherwise, returns an error message.")
  (approve-review-function nil :read-only t :documentation "A function called with this configuration and the
review object that sends an approval to the review service.")
  (shutdown-hook nil :read-only t :documentation "A function to call with no arguments when this
instance of the LGTM UI is shut down.  This can be used to e.g., clean up temporary files."))

;;; * Comments

;; These are the locations that comments are attached to
;;
;; Note: backends may ignore column information if they do not support column granularity
(cl-defstruct lgtm-comment-location
  (version nil :read-only t :documentation "The version of the file the comment is attached to.

This is either \='base or \='current.")
  (file nil :read-only t :documentation "The modified-file to which the comment applies.

This is the immutable modified-file object.  It is here so that service-specific
backends can tell the core program what file the comment is associated with.
This package does not use this field after initialization, preferring instead
to maintain the comment to file mapping as metadata on the modified-file-state.")
  (start-line nil :read-only t :documentation "The line that the comment starts on.")
  (start-column nil :read-only t :documentation "The column that the comment starts on.")
  (end-line nil :read-only t :documentation "The line that the comment ends on.")
  (end-column nil :read-only t :documentation "The column that the comment ends on."))

(defun lgtm-comment-location-at-point (modified-file buffer-version)
  "Create a location based on the current point/region.

The caller must provide the BUFFER-VERSION and the MODIFIED-FILE to
which the comment is attached."
  (let* ((start-position (min (mark) (point)))
         (end-position (max (mark) (point))))
    (cl-assert (or (eq 'base buffer-version) (eq 'current buffer-version)) t "BUFFER-VERSION must be 'base or 'current")
    (make-lgtm-comment-location
     :version buffer-version
     :file modified-file
     :start-line (save-excursion (goto-char start-position) (line-number-at-pos))
     :start-column (save-excursion (goto-char start-position) (current-column))
     :end-line (save-excursion (goto-char end-position) (line-number-at-pos))
     :end-column (save-excursion (goto-char end-position) (current-column)))))

;; These are immutable references to comments.
;;
;; We want this so that they can be used as immutable keys, while the contents can be stored
;; separately and mutable.
(cl-defstruct lgtm-comment-ref
  (id nil :read-only t :documentation "A UUID referencing a (mutable) conversation object"))

;; Comments attached to locations in a changeset.
(cl-defstruct lgtm-comment
  (backend-data nil :documentation "Backend-specific information about the comment.
This is useful for things like the server-side comment id.")
  (ref nil :read-only t :documentation "The immutable reference for this comment.")
  (location nil :read-only t :documentation "The location the comment is attached to.

If this conversation is attached to a file, the location must be a line
number or a range of lines.  Otherwise, the conversation is top-level
and must have a `nil' location.")
  (is-published nil :documentation "Boolean indicating whether or not the comment is published")
  (author nil :read-only t :documentation "The author of the comment.")
  (created-timestamp nil :read-only t :documentation "The time at which the comment was posted.")
  (updated-timestamp nil :read-only t :documentation "The time at which the comment was updated.")
  (parent nil :read-only t :documentation "The parent of the comment, if any.

The parent ID is the backend ID of the parent comment (i.e., the ID used
on the server side).

Note that the hierarchical relationship between comments is parsed when
comments are fetched from the server.")
  (reply-to-id nil :read-only t :documentation "The identifier of the object to reply to when
communicating with the server.  This may or may not be the direct
parent, but this value is passed to the server as the object being
replied to.")
  (content nil :documentation "The content of the comment."))

(cl-defstruct lgtm--comment-manager
  (table (make-hash-table :test 'equal) :read-only t :documentation "The storage for all comments, both
published and unpublished.  The keys are `lgtm-comment-ref' objects.
The values are `lgtm-comment' objects.")
  (top-level-comment-refs '() :documentation "A list of references to all top-level comments.
Note that this includes both published and unpublished comments.  Each comment
has a flag determining whether or not it is published."))

(defun lgtm---add-comment-to-file-unsafe (modified-file-state comment-ref loc)
  "Add COMMENT-REF to the given MODIFIED-FILE-STATE at location LOC.

This version does not do any updates to the selected conversation
indexes, making it generally unsafe as it can violate UI invariants.  It
is intended to be called from `lgtm--add-remote-comments' to add
comments during setup or to be explicitly followed by a step to fix the
related metadata."
  (cl-assert loc t "The comment must have a location")
  (pcase (lgtm-comment-location-version loc)
    ('base (push comment-ref (lgtm--modified-file-state-base-conversations modified-file-state)))
    ('current (push comment-ref (lgtm--modified-file-state-current-conversations modified-file-state)))
    (_ (error "Invalid comment version `%s'" (lgtm-comment-location-version loc)))))

(defun lgtm--sorted-comment-refs (comment-manager modified-file version comment-refs)
  "Sort COMMENT-REFS by thread order.

Returns a list of comment refs in thread order, sorted by using the comment
thread indexer, which requires the COMMENT-MANAGER, MODIFIED-FILE, and VERSION
of the file."
  (let* ((index (lgtm--index-comments-by-ref comment-manager modified-file version comment-refs))
         (linearized-comments (lgtm--get-positioned-comments index)))
    (seq-map (lambda (positioned-comment) (lgtm-comment-ref (lgtm--positioned-comment-comment positioned-comment))) linearized-comments)))

(defun lgtm--add-comment-to-file (comment-manager modified-file-state comment-ref loc)
  "Add COMMENT-REF to the given MODIFIED-FILE-STATE with location LOC.

This assumes that the caller has provided the correct MODIFIED-FILE-STATE.

The COMMENT-MANAGER is required to get the locations (for sorting) of the
other comments.

This function is called when the user completes their comment (see
`lgtm-complete-comment') and to populate the initial set of comments.
It rebuilds the comment order in the file so that indexing continues to
work."
  ;; (cl-assert (equal (lgtm--modified-file-state-ref modified-file-state) (lgtm-comment-location-file comment-ref)) t
  ;;            "Callers must pass a modified-file-state that matches the comment location to lgtm--add-comment-to-file")
  (setf (lgtm--modified-file-state-base-selected-conversation-index modified-file-state) nil)
  (setf (lgtm--modified-file-state-current-selected-conversation-index modified-file-state) nil)

  (lgtm---add-comment-to-file-unsafe modified-file-state comment-ref loc)
  (let ((modified-file (lgtm--modified-file-state-ref modified-file-state))
        (base-conversations (lgtm--modified-file-state-base-conversations modified-file-state))
        (current-conversations (lgtm--modified-file-state-current-conversations modified-file-state)))
    (setf (lgtm--modified-file-state-base-conversations modified-file-state) (lgtm--sorted-comment-refs comment-manager modified-file 'base base-conversations))
    (setf (lgtm--modified-file-state-current-conversations modified-file-state) (lgtm--sorted-comment-refs comment-manager modified-file 'current current-conversations))))

(defun lgtm--add-remote-comments (file-manager comment-manager comments)
  "Add COMMENTS to the internal state.

Save the comments into the COMMENT-MANAGER and use the
FILE-MANAGER to attach each comment to its corresponding
modified file."
  (let ((comment-table (lgtm--comment-manager-table comment-manager))
        (file-table (lgtm--modified-file-manager-table file-manager)))
    (seq-doseq (comment comments)
      (let ((cref (lgtm-comment-ref comment))
            (loc (lgtm-comment-location comment)))
        ;; Add the comment (unless it is already present)
        (unless (gethash cref comment-table)
          (puthash cref comment comment-table)

          (if loc
              (let* ((modified-file-ref (lgtm-comment-location-file loc))
                     (file-state (gethash modified-file-ref file-table)))
                (cl-assert file-state t "Comments with a location must have an associated file")
                (lgtm---add-comment-to-file-unsafe file-state cref loc))
            (push cref (lgtm--comment-manager-top-level-comment-refs comment-manager))))))

    ;; Restore the sorted invariant to all file-level comments
    (seq-doseq (modified-file (lgtm--modified-file-manager-modified-files file-manager))
      (let* ((modified-file-state (lgtm--get-modified-file-state file-manager modified-file))
             (base-conversations (lgtm--modified-file-state-base-conversations modified-file-state))
            (current-conversations (lgtm--modified-file-state-current-conversations modified-file-state)))
        (setf (lgtm--modified-file-state-base-conversations modified-file-state) (lgtm--sorted-comment-refs comment-manager modified-file 'base base-conversations))
        (setf (lgtm--modified-file-state-current-conversations modified-file-state) (lgtm--sorted-comment-refs comment-manager modified-file 'current current-conversations))))))

(defun lgtm--top-level-comments (comment-manager)
  "Get the top-level comments from the COMMENT-MANAGER."
  (let ((tbl (lgtm--comment-manager-table comment-manager))
        (top-level-refs (lgtm--comment-manager-top-level-comment-refs comment-manager)))
    (seq-map (lambda (comment-ref) (gethash comment-ref tbl)) top-level-refs)))

(defun lgtm--top-level-unpublished-comments (comment-manager)
  "Get the unpublished top-level comments from the COMMENT-MANAGER."
  (let ((comments (lgtm--top-level-comments comment-manager)))
    (seq-filter (lambda (comment) (not (lgtm-comment-is-published comment))) comments)))

(defun lgtm--modified-file-base-comments (file-manager comment-manager modified-file)
  "Get the base version comments attached to MODIFIED-FILE.

This requires a FILE-MANAGER to get the mutable file state.
It requires a COMMENT-MANAGER to access the comment states."
  (let* ((mutable-file-state (lgtm--get-modified-file-state file-manager modified-file))
         (base-comment-refs (lgtm--modified-file-state-base-conversations mutable-file-state))
         (tbl (lgtm--comment-manager-table comment-manager)))
    (seq-map (lambda (comment-ref) (gethash comment-ref tbl)) base-comment-refs)))

(defun lgtm--modified-file-current-comments (file-manager comment-manager modified-file)
  "Get the current version comments attached to MODIFIED-FILE.

This requires a FILE-MANAGER to get the mutable file state.
It requires a COMMENT-MANAGER to access the comment states."
  (let* ((mutable-file-state (lgtm--get-modified-file-state file-manager modified-file))
         (current-comment-refs (lgtm--modified-file-state-current-conversations mutable-file-state))
         (tbl (lgtm--comment-manager-table comment-manager)))
    (seq-map (lambda (comment-ref) (gethash comment-ref tbl)) current-comment-refs)))

(defun lgtm--modified-file-comment-count (file-manager comment-manager modified-file)
  "Count the number of comments attached to the given MODIFIED-FILE.
This requires a COMMENT-MANAGER to look up the actual mutable comment state.

This requires a FILE-MANAGER to get the mutable file state."
  (let* ((base-file-comments (lgtm--modified-file-base-comments file-manager comment-manager modified-file))
         (current-file-comments (lgtm--modified-file-current-comments file-manager comment-manager modified-file))
         (all-file-comments (seq-concatenate 'list base-file-comments current-file-comments)))
    (seq-length all-file-comments)))

(defun lgtm--get-comment-content (comment-manager comment-ref)
  "Get the mutable comment state for COMMENT-REF from COMMENT-MANAGER."
  (let* ((tbl (lgtm--comment-manager-table comment-manager)))
    (gethash comment-ref tbl)))

(defun lgtm--comment-manager-add-top-level (comment-manager ref)
  "Add REF as a top-level comment to the COMMENT-MANAGER."
  (setf (lgtm--comment-manager-top-level-comment-refs comment-manager) (cons ref (lgtm--comment-manager-top-level-comment-refs comment-manager))))

(defun lgtm--comment-start-point (buffer comment)
  "Return the start point of COMMENT in the BUFFER."
  (with-current-buffer buffer
    (let ((loc (lgtm-comment-location comment)))
      (save-excursion
        (goto-char (point-min))
        (forward-line (lgtm-comment-location-start-line loc))
        (if (lgtm-comment-location-start-column loc)
            (move-to-column (lgtm-comment-location-start-column loc))
          (back-to-indentation))
        (point)))))

(defun lgtm--comment-end-point (buffer comment)
  "Return the start point of COMMENT in the BUFFER."
  (with-current-buffer buffer
    (let ((loc (lgtm-comment-location comment)))
      (save-excursion
        (goto-char (point-min))
        (forward-line (lgtm-comment-location-end-line loc))
        (if (lgtm-comment-location-end-column loc)
            (move-to-column (lgtm-comment-location-end-column loc))
          (forward-to-indentation))
        (point)))))

;;; * Modified Files


;; Immutable descriptors for each modified file.
;;
;; The filenames do not include the repository path, as we have a reference to the repository.
;; Mutable state associated with modified files is stored in the modified file manager.
(cl-defstruct lgtm--modified-file
  (repository nil :read-only t :documentation "The repository containing the file")
  (type nil :read-only t :documentation "The type of modification applied to the file.
These are symbols based on the modification types from git and are one of:
- modified
- added
- typechange (e.g., regular file, symlink, etc)
- deleted
- renamed
- copied
")
  (current-filename nil :read-only t :documentation "The name of the current file")
  (current-file-hash nil :read-only t :documentation "The git hash of the current file")
  (base-filename nil :read-only t :documentation "The base name of the file if it was renamed or copied.
This is nil for other types of modification.")
  (base-file-hash nil :read-only t :documentation "The git hash of the base file"))


(cl-defstruct lgtm--modified-file-manager
  (table (make-hash-table :test 'equal) :read-only t :documentation "A map containing the state of modified files.
The keys are the immutable `lgtm--modified-file' objects.  The values
are `lgtm--modified-file-state' objects, which are mutable.

Invariant: every file in `modified-files' has an entry in this hash table.")
  (modified-files '() :read-only t :documentation "The list of all modified file handles."))

(defun lgtm--make-modified-file-manager (modified-files)
  "Create an file manager from a list of MODIFIED-FILES."
  (let* ((tbl (make-hash-table :test 'equal)))
    (seq-doseq (modified-file modified-files)
      (let ((file-state (make-lgtm--modified-file-state :ref modified-file)))
        (puthash modified-file file-state tbl)))
    (make-lgtm--modified-file-manager :table tbl :modified-files modified-files)))

(defun lgtm--get-modified-file-state (file-manager modified-file)
  "Get the current mutable state of the given MODIFIED-FILE.

Consults the FILE-MANAGER."
  (let ((modified-file-state-table (lgtm--modified-file-manager-table file-manager)))
    (gethash modified-file modified-file-state-table)))


(cl-defstruct lgtm--file-review-state-backend
  "An adapter to track the review state of modified files.

This adapter is called when the user marks a file in a changeset as
reviewed or unreviewed.  This functionality is encapsulated in an
adapter because some users will not want read-state persistence and some
backends may support tracking this state on the server.

The API only takes the `lgtm-modified-file' as an input.  If a backend
that supports server-side storage needs more information (e.g., a
changeset ID) it should be captured in closure state when the adapter is
created."
  (mark-reviewed (lambda (_modified-file) nil) :read-only t :documentation "Mark the given modified-file as reviewed.")
  (mark-unreviewed (lambda (_modified-file) nil) :read-only t :documentation "Mark the given modified-file as unreviewed.")
  (file-reviewed-p (lambda (_modified-file) nil) :read-only t :documentation "Test if the given file has been reviewed or not."))

(defun lgtm--make-no-op-review-state-backend ()
  "A no-op adapter for the review state backend.

This backend discards all state changes."
  (make-lgtm--file-review-state-backend))

(defconst lgtm--sqlite-review-state-create-table-query
  "CREATE TABLE IF NOT EXISTS review_state (base_revision TEXT, current_revision TEXT, timestamp INTEGER, PRIMARY KEY (base_revision, current_revision))")

(defun lgtm--sqlite-review-state-backend-file-hash (modified-file field-accessor)
  "For the given MODIFIED-FILE and FIELD-ACCESSOR, return the hash.

If the change is an addition or a deletion of MODIFIED-FILE, return
either \='added or \='deleted for the missing hash.

We need to have a non-nil value for both revisions in the SQLite table,
as those fields are part of the composite primary key."
  (let ((the-hash (funcall field-accessor modified-file)))
    (if the-hash
        the-hash
      (pcase (lgtm--modified-file-type modified-file)
        ('added "added")
        ('deleted "deleted")
        (_ (error "Invariant violation: the file hash should only be missing for an added or deleted file: %s" modified-file))))))

(defun lgtm--make-sqlite-review-state-backend (db-file)
  "A local sqlite adapter for the review state backend.

The database will be named DB-FILE.  This assumes that the caller has
already validated that sqlite is available.

A file is marked as reviewed if it has an entry in the `review_state'
table.  Each entry is keyed by the git hash of the base revision and the
current revision of the file.  This accommodates additions and deletions
and also ensures that files reviewed in an earlier revision of a
changeset are preserved as long as their hash does not change."
  (require 'sqlite)
  (cl-assert db-file t "The database file must be specified")
  (let ((db (sqlite-open db-file)))
    (sqlite-execute db lgtm--sqlite-review-state-create-table-query)
    (let ((mark-reviewed (lambda (modified-file)
                           (let ((base (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-base-file-hash))
                                 (current (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-current-file-hash)))
                             (sqlite-execute db "INSERT INTO review_state VALUES (?, ?, unixepoch(CURRENT_TIMESTAMP))" `(,base ,current)))))
          (mark-unreviewed (lambda (modified-file)
                             (let ((base (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-base-file-hash))
                                   (current (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-current-file-hash)))
                               (sqlite-execute db "DELETE FROM review_state WHERE base_revision = ? AND current_revision = ?" `(,base ,current)))))
          (file-reviewed-p (lambda (modified-file)
                             (let* ((base (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-base-file-hash))
                                    (current (lgtm--sqlite-review-state-backend-file-hash modified-file #'lgtm--modified-file-current-file-hash))
                                    (results (sqlite-select db "SELECT timestamp FROM review_state WHERE base_revision = ? AND current_revision = ?" `(,base ,current))))
                               (> (length results) 0)))))
      (make-lgtm--file-review-state-backend
       :mark-reviewed mark-reviewed
       :mark-unreviewed mark-unreviewed
       :file-reviewed-p file-reviewed-p))))

;;; * Top-level application state

;; The data associated with a review
(cl-defstruct lgtm--state
  "All of the state associated with a review.

There is a single global instance of this value."
  (configuration nil :read-only t :documentation "The configuration of this review.")
  (active-reviewed-file nil :documentation "The file actively being reviewed with the ediff session.")
  (comment-being-edited nil :documentation "The reference to the conversation currently being edited.")
  (current-revision-buffer nil :documentation "The buffer containing the current revision contents of the
file currently being reviewed.")
  (base-revision-buffer nil :documentation "The buffer containing the base revision contents of the
file currently being reviewed.")
  (draft-review-id nil :documentation "This is an opaque identifier for the review.

This is used as a handle to the state for the current review state on the
server. This field is lazily populated when the first operation that
requires it is executed.")
  (comment-manager (make-lgtm--comment-manager) :read-only t :documentation "The manager/index of all comments in the review.")
  (file-manager (make-lgtm--modified-file-manager) :read-only t :documentation "The manager/index of all modified files in the review.")
  (review-file-buffers '() :documentation "The buffers created to review individual files in the changeset.

We track these buffers so that we can clean them up when shutting down lgtm to
avoid endlessly accumulating review buffers.  Note that we try to clean up
buffers incrementally when ediff views are closed, but we also do a pass at
the end in case any buffers are missed.

[tag:buffer-cleanup]"))

(defun lgtm--get-selected-buffer-tag (state)
  "Get the tag of the active buffer.

This requires STATE for the references to the base/current buffers.
This function returns the buffer tag corresponding to the buffer the point
is currently in.  The result is one of:
- \='base
- \='current
- nil

This returns nil if no file is actively being reviewed."
  (let ((active-file (lgtm--state-active-reviewed-file state)))
    (if active-file
        (if (eq (current-buffer) (lgtm--state-base-revision-buffer state)) 'base 'current)
      nil)))

(defun lgtm--make-default-config ()
  "Create a default configuration.

This assumes that the working directory is the root of the git repository
associated with the change.  Note that this default is not able to submit
reviews or fetch remote conversations.  This configuration is only useful
for experimentation.  See the forge-specific backends for other options.

Note that this can be useful for experimentation but is not useful for
day-to-day work, as it does not have a connection to a changeset host."
  (let* ((commits (lgtm--compute-change-commits default-directory "HEAD~1"))
         (repo (make-lgtm-repository :base-revision "HEAD~1" :path default-directory :name default-directory :commits commits)))
    (make-lgtm-configuration
     :user (user-login-name)
     :changeset-id 'default
     :repositories (list repo)
     :changeset-description (shell-command-to-string "git log -1"))))


(defun lgtm--parse-modified-type (type-string)
  "Parse TYPE-STRING into a modified type symbol.

This only inspects the first character of the modification type.  There
are sometimes modifier suffixes that we don't need to account for, but
that we don't want to error on."
  (pcase (substring type-string 0 1)
    ("M" 'modified)
    ("A" 'added)
    ("D" 'deleted)
    ("T" 'typechange)
    ("R" 'renamed)
    ("C" 'copied)
    (_ (error "Unsupported file modification type `%s`" type-string))))

(defun lgtm--hash-of-file-at-revision (filename revision)
  "Compute the hash of the given FILENAME at the given REVISION.

This currently uses git `ls-tree', which returns an output in the form:
<mode> <type> <hash> <filename>."
  (let* ((cmd (format "git ls-tree %s '%s'" revision filename))
         (git-output (shell-command-to-string cmd))
         (fields (string-split git-output)))
    (elt fields 2)))

(defconst lgtm--parse-git-short-commit-rx "^\\([[:xdigit:]]+\\) \\(.*\\)")

(defun lgtm--parse-git-short-commit (line)
  "Parse a LINE from git short log output.

This produces a pair (commit . commit-message)."
  (if (string-match lgtm--parse-git-short-commit-rx line)
      (let ((commit-hash (match-string 1 line))
            (message (match-string 2 line)))
        (cons commit-hash message))
    (error "Could not parse short git log entry %s" line)))

(defun lgtm--parse-git-file-status (repository git-modified-entry)
  "Parse a git diff status entry.
Parses GIT-MODIFIED-ENTRY into a `lgtm--modified-file' referencing
the containing REPOSITORY.

This assumes that the working directory is set to the repository
containing the file."
  (let ((elements (split-string git-modified-entry)))
    (pcase elements
      (`(,type ,filename) (make-lgtm--modified-file
                           :repository repository
                           :type (lgtm--parse-modified-type type)
                           :current-filename filename
                           :current-file-hash (lgtm--hash-of-file-at-revision filename "HEAD")
                           :base-file-hash (lgtm--hash-of-file-at-revision filename (lgtm-repository-base-revision repository))))
      (`(,type ,base-filename ,filename) (make-lgtm--modified-file
                                          :repository repository
                                          :type (lgtm--parse-modified-type type)
                                          :current-filename filename
                                          :current-file-hash (lgtm--hash-of-file-at-revision filename "HEAD")
                                          :base-filename base-filename
                                          :base-file-hash (lgtm--hash-of-file-at-revision base-filename (lgtm-repository-base-revision repository))))
      (_ (error "Unhandled git modification entry `%s`" git-modified-entry)))))

(defun lgtm--compute-repository-modified-files (repository)
  "Return a list of all of the modified files in the given Git REPOSITORY."
  (let* ((default-directory (lgtm-repository-path repository))
         (git-diff-command (format "git diff --name-status %s..HEAD" (lgtm-repository-base-revision repository)))
         (git-output (shell-command-to-string git-diff-command))
         (entry-list (split-string (string-trim git-output) "\n")))
    (seq-map (lambda (it) (lgtm--parse-git-file-status repository it)) entry-list)))

(defun lgtm--compute-change-commits (repository-dir base-revision)
  "Return a list of commits in the changeset.

The commits are computed for the repository at REPOSITORY-DIR between
the current revision on disk and the BASE-REVISION.  This helper is
intended to be used when constructing a `lgtm-repository' object."
  (let* ((default-directory repository-dir)
         (cmd (format "git log --oneline --no-decorate --no-abbrev-commit %s..HEAD" base-revision))
         (git-output (shell-command-to-string cmd))
         (entry-list (split-string (string-trim git-output) "\n")))
    (seq-map #'lgtm--parse-git-short-commit entry-list)))

(defun lgtm--compute-modified-files (repositories)
  "Return a list of all modified files in the list of REPOSITORIES."
  (seq-mapcat #'lgtm--compute-repository-modified-files repositories))

(defun lgtm--format-comment-count (count)
  "Format comment count COUNT suitably for display in the UI.

We include the space here under the assumption that the caller accounts for it."
  (if (eql count 0) "" (format " (%d)" count)))

(defun lgtm--format-file-modification-type (ty)
  "Format the file modification type symbol.

Format TY as a string suitable for display in the UI."
  (pcase ty
    ('modified "M")
    ('added "A")
    ('deleted "D")
    ('typechange "T")
    ('renamed "R")
    ('copied "C")
    (_ (error "Invalid file modification type `%s'" ty))))

(defun lgtm--format-file-review-status (file-review-status)
  "Format the modification status FILE-REVIEW-STATUS for the UI."
  (if file-review-status "✓" " "))

(defun lgtm--format-modified-file-diff (modified-file)
  "Format the diff for a single MODIFIED-FILE.

This diff is meant to be used in the main UI as a preview of the change."
  (let* ((default-directory (lgtm-repository-path (lgtm--modified-file-repository modified-file)))
         (current-filename (lgtm--modified-file-current-filename modified-file))
         (base-filename (lgtm--modified-file-base-filename modified-file))
         (real-base-filename (if base-filename base-filename current-filename))
         (base-revision (lgtm-repository-base-revision (lgtm--modified-file-repository modified-file))))

    (pcase (lgtm--modified-file-type modified-file)
      ('deleted (let ((git-diff-command (format "git diff %s -- %s" base-revision real-base-filename)))
                  (string-trim (shell-command-to-string git-diff-command))))
      ('added (let ((git-diff-command (format "git diff %s -- %s" base-revision real-base-filename)))
                  (string-trim (shell-command-to-string git-diff-command))))
      (_ (let ((git-diff-command (format "git diff %s:'%s'..HEAD:'%s'" base-revision real-base-filename current-filename)))
           (string-trim (shell-command-to-string git-diff-command)))))))

(defun lgtm--format-modified-file (state modified-file)
  "Create the top-level description for MODIFIED-FILE.

The STATE is required here to access saved review comments."
  (let* ((comment-manager (lgtm--state-comment-manager state))
         (file-manager (lgtm--state-file-manager state))
         (review-state-backend (lgtm-configuration-review-state-backend (lgtm--state-configuration state)))
         (current-filename (lgtm--modified-file-current-filename modified-file))
         (base-filename (lgtm--modified-file-base-filename modified-file))
         (comment-count (lgtm--modified-file-comment-count file-manager comment-manager modified-file))
         (comment-count-string (lgtm--format-comment-count comment-count))
         (modification-type (lgtm--modified-file-type modified-file))
         (modification-type-string (lgtm--format-file-modification-type modification-type))
         (modification-status-string (lgtm--format-file-review-status (funcall (lgtm--file-review-state-backend-file-reviewed-p review-state-backend) modified-file))))
    (pcase modification-type
      ((or 'renamed 'copied) (format "  %s [%s] %s -> %s%s" modification-status-string modification-type-string base-filename current-filename comment-count-string))
      (_ (format "  %s [%s] %s%s" modification-status-string modification-type-string current-filename comment-count-string)))))

;;; Generic Trees

(cl-defstruct lgtm--tree
  "A simple n-ary tree data structure.

While it is easy to represent trees in elisp using nested lists, this
explicit structure makes the intent clearer.  The empty tree is represented
by nil."
  (value nil :read-only t :documentation "The value at this tree node")
  (children '() :documentation "The children of this tree node"))

(defun lgtm--tree-add-child (tree c)
  "Add child element C to tree TREE."
  (push c (lgtm--tree-children tree)))

;;; Comment Indexing


(cl-defstruct lgtm--positioned-comment
  "The hierarchical position of a comment.

This reflects the linear order (index) of the comment in the file and
also the indentation level respecting reply structure.  The `comment' is
a pointer to the full comment (and not a `lgtm-comment-ref').  While most
references to comments should be via `lgtm-comment-ref', this is a
transient structure."
  (index nil :read-only t :documentation "The unique index of the comment in the file")
  (indent nil :read-only t :documentation "The indentation level to render the comment at")
  (comment nil :read-only t :documentation "The comment for which this metadata applies"))

;; This structure contains a per-file index of comments
;;
;; The index assigned to each comment reflects relative sort order (determined by a combination of
;; thread structure and time)
;;
;; Note that this structure is computed as a local temporary index and thus contains a pointer to
;; the underlying comment, rather than a comment-ref.
(cl-defstruct lgtm--comment-index
  "A transient data structure to compute the nesting relation between comments."
  (modified-file nil :read-only t :documentation "The reference to the file containing the indexed comments")
  (version nil :read-only t :documentation "The version (base or current) of the file containing the indexed comments")
  (comment-threads-by-location nil :read-only t :documentation "Computed metadata for each comment to aid rendering"))

(defun lgtm--comment-index-traverse-from-root (idx depth tree-node)
  "Traverse the TREE-NODE depth-first to create a comment list.

Index each element starting from IDX.  Each `lgtm--positioned-comment'
wraps a comment with metadata (including an assigned DEPTH)."
  (let ((this-pos-comment (make-lgtm--positioned-comment :index idx :indent depth :comment (lgtm--tree-value tree-node))))
    (seq-let [next-idx dfs-children] (seq-reduce (lambda (accum child)
                                                   (seq-let [accum-idx accum-items] accum
                                                     (seq-let [seq-next-idx these-items] (lgtm--comment-index-traverse-from-root accum-idx (+ 1 depth) child)
                                                       (list seq-next-idx (seq-concatenate 'list accum-items these-items)))))
                                                 (lgtm--tree-children tree-node)
                                                 (list (+ 1 idx) '()))
      (list next-idx (cons this-pos-comment dfs-children)))))

(defun lgtm--index-comments (comments)
  "Create an index of COMMENTS and the metadata required to render them.

This is a helper for `lgtm--index-comments-by-ref' that works on fully
resolved comments.  The returned alist is sorted by location."
  (let* (;; Map comment-refs to the tree node representing them
         (comment-ref-to-tree (make-hash-table :test 'equal))
         ;; Map (server-side) comment ids to internal comment-ref structures
         (comment-id-to-comment-ref (make-hash-table :test 'equal))
         ;; The (list of) root comments for each location. This is used to collect comment roots
         ;; during the indexing phase so that each comment thread/tree can be traversed in-order
         ;; later.
         ;;
         ;; Invariant: if there is an entry for a location, the list is non-empty
         (location-roots (make-hash-table :test 'equal)))

    (seq-doseq (comment comments)
      (let* ((backend-id (lgtm-comment-backend-data comment))
             (tree-node (make-lgtm--tree :value comment))
             (comment-ref (lgtm-comment-ref comment)))
        (puthash comment-ref tree-node comment-ref-to-tree)
        ;; If the comment doesn't have a server ID, it can't have any replies
        (when backend-id
          (puthash backend-id comment-ref comment-id-to-comment-ref))))

    ;; After we index everything, we can then traverse the comments to compute reply structure. We
    ;; want to have the index first so that we can pre-allocate all of the tree nodes.
    (seq-doseq (comment comments)
      (let* ((parent-id (lgtm-comment-parent comment))
             (comment-ref (lgtm-comment-ref comment))
             (comment-tree-node (gethash comment-ref comment-ref-to-tree))
             (loc (lgtm-comment-location comment)))

        (if parent-id
            ;; Set up the parent structure if there is a parent
            (let* ((parent-node-ref (gethash parent-id comment-id-to-comment-ref))
                   (parent-tree-node (gethash parent-node-ref comment-ref-to-tree)))
              (lgtm--tree-add-child parent-tree-node comment-tree-node))
          ;; Otherwise this is a root we need to record
          (if (gethash loc location-roots)
              (push comment-ref (gethash loc location-roots))
            (puthash loc (list comment-ref) location-roots)))))

    ;; Now sort all of the child lists by timestamp so that they render sensibly
    (let ((sort-key (lambda (tree-node) (lgtm-comment-created-timestamp (lgtm--tree-value tree-node)))))
      (maphash (lambda (_comment-id tree-node)
                 (let ((sorted-children (seq-sort-by sort-key #'value< (lgtm--tree-children tree-node))))
                   (setf (lgtm--tree-children tree-node) sorted-children)))
               comment-ref-to-tree))

    (let ((index-source 0)
          (location-comments-alist '()))
      (maphash (lambda (loc comment-refs-at-loc)
                 (seq-doseq (comment-root-ref comment-refs-at-loc)
                   (let ((comment-root (gethash comment-root-ref comment-ref-to-tree)))
                     (seq-let [next-idx linearized-comments] (lgtm--comment-index-traverse-from-root index-source 0 comment-root)
                       (setf index-source next-idx)
                       (push linearized-comments (alist-get loc location-comments-alist '() nil 'equal))))))
               location-roots)
      (seq-sort-by (lambda (pair) (lgtm-comment-location-start-line (car pair))) #'< location-comments-alist))))


(defun lgtm--index-comments-by-ref (comment-manager modified-file version comment-refs)
  "Create an index of COMMENT-REFS and metadata required to render them.

The COMMENT-MANAGER is required to get the comment bodies given a comment-ref.
The MODIFIED-FILE and VERSION are kept for tracking and debugging but are not
critical."
  (let* ((comments (seq-map (lambda (comment-ref) (lgtm--get-comment-content comment-manager comment-ref)) comment-refs))
         (comments-by-loc (lgtm--index-comments comments)))
    (make-lgtm--comment-index :modified-file modified-file :version version :comment-threads-by-location comments-by-loc)))

(defun lgtm--get-positioned-comments (comment-index)
  "Extract a linearized list of (location, comment-list) pairs from COMMENT-INDEX.

Each list contains `lgtm--positioned-comment' values in display order."
  (seq-mapcat (lambda (alist) (seq-mapcat (lambda (l) l) (cdr alist))) (lgtm--comment-index-comment-threads-by-location comment-index)))

(cl-defstruct lgtm--git-repository-commit-history
  (inferred-base-commit nil :read-only t :documentation "The base commit in the history against
which the other commits are applied.")
  (change-commits nil :read-only t :documentation "The commits applied by the changeset to
this repository."))

(defun lgtm--get-commits-from-HEAD (repository-path max-count)
  "Return the sequence of commits from REPOSITORY-PATH.

The sequence is computed from HEAD of the current branch.  Each commit
is a pair of (commit-hash, commit-message).  Limits the query to MAX-COUNT
entries for efficiency."
  (let* ((default-directory repository-path)
         ;; We use --no-abbrev-commit to get full-length commit hashes
         (history-command (format "git log --max-count=%d --oneline --no-decorate --no-abbrev-commit" max-count))
         (git-output (shell-command-to-string history-command))
         (entry-list (split-string (string-trim git-output) "\n")))
    (seq-map #'lgtm--parse-git-short-commit entry-list)))

(defun lgtm--assign-commits-to-repository-histories (history-index-alist commits)
  "Analyze the HISTORY-INDEX-ALIST to create `lgtm-repository' values.

This maps each commit hash in COMMITS to their respective repositories
and calculates the parent commit for each set of commits.  The return
value is a list of `lgtm-repository'.

The HISTORY-INDEX-ALIST maps each path to a git repository on disk to
the list of (commit-hash, commit-message) pairs in the commit history.

Note that this does not attempt to do any validity checking for the
provided commits (e.g., that commits are sequential in the history of
a repository)."
  (let ((history-table (make-hash-table))
        (referenced-commits-table (make-hash-table)))
    ;; Convert the history index into a hash table for faster lookup.  Also ensure that the commit
    ;; history is in a vector, as we are going to do linear searches and index into them.
    (seq-doseq (hist-entry history-index-alist)
      (puthash (car hist-entry) '() referenced-commits-table)
      (puthash (car hist-entry) (seq-into (cdr hist-entry) 'vector) history-table))

    (seq-doseq (commit commits)
      (catch 'lgtm-found-commit-repository
        (maphash (lambda (repository-path commit-vec)
                   ;; Each history item is actually a (commit-hash, commit-message) pair, so we need
                   ;; a special comparator
                   (let ((found-index (seq-position commit-vec commit (lambda (history-item target) (equal (car history-item) target)))))
                     (when found-index
                       (let ((commits-in-repo (gethash repository-path referenced-commits-table)))
                         (puthash repository-path (cons found-index commits-in-repo) referenced-commits-table))
                       (throw 'lgtm-found-commit-repository t))))
                 history-table)
        (warn "Unable to find the repository containing commit `%s'" commit)))

    ;; Sort the lists of referenced commit indices so that the last one is the oldest commit.
    (maphash (lambda (repository-path referenced-commit-indices)
               (let ((sorted (seq-sort #'value< referenced-commit-indices)))
                 (puthash repository-path sorted referenced-commits-table)))
             referenced-commits-table)

    (let ((repositories (seq-map (lambda (hist-entry)
                                   (let* ((repository-path (car hist-entry))
                                          (commit-indices (gethash repository-path referenced-commits-table))
                                          (repository-commits (gethash repository-path history-table))
                                          (commit-hashes (seq-map (lambda (idx) (elt repository-commits idx)) commit-indices)))
                                     (if (equal (length commit-indices) 0)
                                         (progn
                                           (warn "No commits found for repository `%s'" repository-path)
                                           nil)
                                       (let* ((last-referenced-commit-index (elt commit-indices (- (length commit-indices) 1)))
                                              (base-revision (car (elt repository-commits (+ 1 last-referenced-commit-index)))))
                                         (make-lgtm-repository :base-revision base-revision
                                                               :name (file-name-nondirectory (directory-file-name repository-path))
                                                               :commits commit-hashes
                                                               :path repository-path)))))
                                 history-index-alist)))
      (seq-sort-by #'lgtm-repository-name #'string< (seq-filter #'identity repositories)))))

(defun lgtm--assign-commits-to-repositories (repository-paths commits)
  "Assign a list of COMMITS to a list of REPOSITORY-PATHS.

The result is a hash table mapping each repository to commit
metadata.  The metadata includes the list of commits from COMMITS
in order and, separately, the base commit that the sequence of commits
is applied against in the repository history.

This returns a list of `lgtm-repository' objects.

This function is a wrapper around the real worker
function (`lgtm--assign-commits-to-repository-histories') that handles
interacting with git repositories."
  (seq-doseq (repository-path repository-paths)
    (cl-assert (file-name-absolute-p repository-path) t "All repository paths must be absolute"))

  (let* ((max-count (+ (length commits) (length repository-paths)))
         (history-index-alist (seq-map (lambda (repository-path) (cons repository-path (lgtm--get-commits-from-HEAD repository-path max-count))) repository-paths)))
    (lgtm--assign-commits-to-repository-histories history-index-alist commits)))

(provide 'lgtm-core)

;;; lgtm-core.el ends here
