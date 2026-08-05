;;; lgtm-github.el --- Github adapter for lgtm -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Tristan Ravitch

;; Author: Tristan Ravitch <tristan@ravit.ch>
;; Maintainer: Tristan Ravitch <tristan@ravit.ch>
;; URL: https://github.com/travitch/lgtm.el
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (ghub "4.3.0")
;; Keywords: convenience tools


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

;; This package provides a magit-like `ediff' derived interface for reviewing Github PRs

;;; Code:

;;;; Requirements

(require 'cl-lib)
(require 'ghub)
(require 'ghub-graphql)

(require 'lgtm)
(require 'lgtm-core)

;;; Constants

(defconst lgtm-github--pr-url-rx "^https://github.com/\\([[:alnum:]-_]+\\)/\\([[:alnum:]-_.]+\\)/pull/\\([[:digit:]]+\\)$")

(defconst lgtm-github--pr-ref-rx "^refs/pull/\\([0-9]+\\)/head$")

(defconst lgtm-github--remote-git-url-rx "^git@github.com:\\([^/]+\\)/\\(.*\\).git$")

(defconst lgtm-github--remote-https-url-rx "^https://github.com/\\([^/]+\\)/\\(.*\\)$")

(defconst lgtm-github--get-pr-info-query
  '(query
    (repository [(owner $owner String!) (name $name String!)]
                (pullRequest [(number $number Int!)]
                             id
                             body
                             number
                             state
                             createdAt
                             title
                             (author login)
                             baseRefOid
                             baseRefName
                             url))))

(defconst lgtm-github--get-pr-comments-query
  '(query
    (repository [(owner $owner String!) (name $name String!)]
                (pullRequest [(number $number Int!)]
                             (reviewThreads [(:edges t)] diffSide id startLine line path
                                            (comments [(:edges t)] (author login) body createdAt id (replyTo id fullDatabaseId) updatedAt fullDatabaseId))))))

(defconst lgtm-github--get-pr-top-level-comments-query
  '(query
    (repository [(owner $owner String!) (name $name String!)]
                (pullRequest [(number $number Int!)]
                             (comments [(:edges t)] (author login) body createdAt id updatedAt)))))

;; A query to get the review comments left by the user (review author) on the currently pending
;; review.
;;
;; [tag:get-review-comments-query]
(defconst lgtm-github--get-current-review-comments-query
  '(query
    (repository [(owner $owner String!) (name $name String!)]
                (pullRequest [(number $number Int!)]
                             (reviews [(:edges t) (author $author String!) (states $states [PullRequestReviewState!]!)]
                                      (comments [(:edges t)] id fullDatabaseId body path createdAt updatedAt line startLine (replyTo id fullDatabaseId) state))))))

;;; Implementation

(defun lgtm-github--graphql-select (data lineage)
  "Extract the subset of the data described by LINEAGE from the DATA response."
  (catch 'strip-path-no-match
    (while-let ((key (pop lineage)))
      (pcase key
        ((guard (numberp key))
         (setq data (elt data key)))
        ((guard (and (consp key) (symbolp (cdr key))))
         (if (eq (car key) (car data))
                (let ((matched (seq-find (lambda (obj) (equal (car obj) (cdr key))) (cdr data))))
                  (setq data (car (cdr matched))))
           (throw 'strip-path-no-match nil)))
        ((guard (and (consp key) (numberp (cdr key))))
         (if (eq (car key) (car data))
             (let ((val (seq-elt (cdr data) (cdr key))))
               (setq data val))
           (throw 'strip-path-no-match nil)))
        ((guard (symbolp key))
         (if (eq key (car data))
             (progn
               (setq data (cdr data)))
           (throw 'strip-path-no-match nil)))
        (_ (error "Invalid key type %s" key))))
      data))

;; A parsed PR URL
(cl-defstruct lgtm-github--repo-pr
  (repository nil :read-only t :documentation "The repository containing the PR")
  (pr-num nil :read-only t :documentation "The PR number"))

(defun lgtm-github--parse-pr-url (string)
  "Parse the STRING into a repo-pr.

The supported format is e.g., https://github.com/travitch/bytepype/pull/1"
  (if (string-match lgtm-github--pr-url-rx string)
      (let* ((owner (match-string 1 string))
             (repo-name (match-string 2 string))
             (pr-number (match-string 3 string))
             (repo (make-lgtm-github--repository :owner owner :repo repo-name)))
        (make-lgtm-github--repo-pr :repository repo :pr-num pr-number))
      nil))

;; A pull request ref
(cl-defstruct lgtm-github--pr-ref
  (hash nil :read-only t :documentation "The hash of the PR commit")
  (pr-number nil :read-only t :documentation "The PR number"))

(defun lgtm-github--parse-pr-ref (string)
  "Parse the STRING into a PR descriptor.

The output is in the form:

> <hash>  <ref-name>

Ref names look like with refs/pull/$NUMBER/head."
  (let* ((components (string-split string))
         (hash (elt components 0))
         (ref-name (elt components 1)))
    (if (string-match lgtm-github--pr-ref-rx ref-name)
        (let ((pr-number (match-string 1 ref-name)))
          (make-lgtm-github--pr-ref :hash hash :pr-number pr-number))
      nil)))

(defun lgtm-github--get-prs ()
  "Parse remote refs to enumerate PRs."
  (let* ((git-output (string-trim (shell-command-to-string "git ls-remote -q")))
         (entry-strings (string-split git-output "\n"))
         (parsed-entries (seq-map #'lgtm-github--parse-pr-ref entry-strings)))
    (seq-filter (lambda (p) (not (eq nil p))) parsed-entries)))

(defun lgtm-github--get-current-hash ()
  "Get the commit hash for HEAD."
  (let ((git-output (shell-command-to-string "git rev-parse HEAD")))
    (string-trim git-output)))

(cl-defstruct lgtm-github--repository
  (owner nil :read-only t :documentation "The owner of the Github repository")
  (repo nil :read-only t :documentation "The name of the Github repository"))

(defun lgtm-github--parse-origin-url (rx origin-url)
  "Parse the ORIGIN-URL with the RX to create a repository."
      (if (string-match rx origin-url)
        (let ((owner (match-string 1 origin-url))
              (repo (match-string 2 origin-url)))
          (make-lgtm-github--repository :owner owner :repo repo))
      nil))

;; Parse 'git remote get-url origin'
;;
;; git@github.com:OWNER/REPO.git
(defun lgtm-github--get-repository ()
  "Get the owner/repo of the repository in the current directory.

NOTE: This currently only works if the github remote is named `origin'.
This assumes that the URL is in the format git@github.com:USER/REPO.git."
  (let* ((origin-url (string-trim (shell-command-to-string "git remote get-url origin")))
         (git-protocol-parse (lgtm-github--parse-origin-url lgtm-github--remote-git-url-rx origin-url)))
    (if git-protocol-parse
        git-protocol-parse
      (let ((https-parse (lgtm-github--parse-origin-url lgtm-github--remote-https-url-rx origin-url)))
        (if https-parse
            https-parse
          (error "Failed to parse origin URL `%s'" origin-url))))))

(defun lgtm-github--get-github-username ()
  "Get the Github username configured in `git config'."
  (string-trim (shell-command-to-string "git config github.user")))

(cl-defstruct lgtm-github--pr-info
  (id nil :read-only t :documentation "The GitHub node_id of the PR")
  (owner nil :read-only t :documentation "The owner of the repository")
  (repository-name nil :read-only t :documentation "The name of the repository")
  (number nil :read-only t :documentation "The PR number")
  (body nil :read-only t :documentation "The raw body of the PR description")
  (state nil :read-only t :documentation "The state of the PR (open, closed, etc)")
  (created-at nil :read-only t :documentation "The timestamp at which the PR was created")
  (title nil :read-only t :documentation "The title of the PR")
  (author-login nil :read-only t :documentation "The login of the author of the PR")
  (base-ref nil :read-only t :documentation "The git ref the PR applies to")
  (base-ref-name nil :read-only t :documentation "The name of the base ref")
  (url nil :read-only t :documentation "The URL to the PR")
  (review-id nil :documentation "The identifier of the pending review, if any.

This is nil when there is no pending review.
It gets updated as the review evolves."))

(defun lgtm-github--get-pr-info (repository pr-descriptor)
  "Query the Github API to get information for the given PR-DESCRIPTOR.

Also takes a Github REPOSITORY."
  (let* ((owner (lgtm-github--repository-owner repository))
         (repo (lgtm-github--repository-repo repository))
         (pull-number (lgtm-github--pr-ref-pr-number pr-descriptor))
         (variables `((owner . ,owner) (name . ,repo) (number . ,(string-to-number pull-number))))
         (raw-response (ghub-query lgtm-github--get-pr-info-query variables :auth 'lgtm :synchronous t))
         (narrowed-response (lgtm-github--graphql-select raw-response '((data . 0) (repository . 0) pullRequest))))
    (let-alist narrowed-response
      (make-lgtm-github--pr-info
       :id .id
       :body .body
       :owner owner
       :repository-name repo
       :number .number
       :state .state
       :created-at (lgtm-github--parse-timestamp .createdAt)
       :title .title
       :author-login .author.login
       :base-ref .baseRefOid
       :base-ref-name .baseRefName
       :url .url))))

(defun lgtm-github--parse-review-comment (file-manager comment-item)
  "Parse COMMENT-ITEM into a `lgtm-comment'.

This requires the FILE-MANAGER to map the location back
to a `lgtm-modified-file'."
  (let-alist comment-item
    (let* ((version (lgtm-github--get-comment-revision .diffSide))
           (file (lgtm-github--get-file-of-change file-manager version .path))
           (loc (make-lgtm-comment-location :version version :file file :start-line .startLine :end-line .line)))
      (make-lgtm-comment
       :ref (make-lgtm-comment-ref :id .id)
       :backend-data .id
       :location loc
       :is-published (equal .state "SUBMITTED")
       :content .body
       :author .author.login
       :parent .replyTo.id
       :reply-to-id .id
       :created-timestamp (lgtm-github--parse-timestamp .createdAt)
       :updated-timestamp (lgtm-github--parse-timestamp .updatedAt)))))

(defun lgtm-github--parse-server-comment (loc comment-item)
  "Construct an internal comment from a Github GraphQL COMMENT-ITEM.

The LOC is passed in because it is already parsed.  The THREAD-ID is the
identifier for the thread containing the comment.  This is important as
replies to any comment in this thread should be attached to this thread
id."
  (let-alist comment-item
    (let ((ref (make-lgtm-comment-ref :id (string-to-number .fullDatabaseId))))
      (make-lgtm-comment
       :ref ref
       :backend-data (string-to-number .fullDatabaseId)
       :is-published t
       :location loc
       :content .body
       :author .author.login
       :parent (if .replyTo.fullDatabaseId (string-to-number .replyTo.fullDatabaseId) nil)
       :reply-to-id (string-to-number .fullDatabaseId)
       :created-timestamp (lgtm-github--parse-timestamp .createdAt)
       :updated-timestamp (lgtm-github--parse-timestamp .updatedAt)))))

(defun lgtm-github--parse-comment-thread (file-manager thread-item)
  "Parse THREAD-ITEM from the server into a list of comments for the thread.

The FILE-MANAGER is used to map comments back to the internal representation
of source files."
  (let-alist thread-item
    (let* ((version (lgtm-github--get-comment-revision .diffSide))
           (file (lgtm-github--get-file-of-change file-manager version .path))
           (loc (make-lgtm-comment-location :version version :file file :start-line .startLine :end-line .line))
           (flattened-comments-list .comments))
      (if (and version file)
          (seq-map (lambda (comment-item) (lgtm-github--parse-server-comment loc comment-item)) flattened-comments-list)
        (progn
          (warn "Could not determine version or file for comment thread %s" thread-item)
          nil)))))

(defun lgtm-github--parse-top-level-comment-thread (comment-item)
  "Parse COMMENT-ITEM from the server into a list of comments for the thread."
  (let-alist comment-item
    (let ((ref (make-lgtm-comment-ref :id .id)))
      (make-lgtm-comment
       :ref ref
       :backend-data .id
       :is-published t
       :content .body
       :author .author.login
       :created-timestamp (lgtm-github--parse-timestamp .createdAt)
       :updated-timestamp (lgtm-github--parse-timestamp .updatedAt)))))

(defun lgtm-github--get-pr-comments (file-manager repository pr-descriptor)
  "Fetch comments for the PR-DESCRIPTOR from the REPOSITORY.

The results are parsed into internal comment structures.  The FILE-MANAGER is
required to map file names to file objects."
  (let* ((owner (lgtm-github--repository-owner repository))
         (repo (lgtm-github--repository-repo repository))
         (pull-number (string-to-number (lgtm-github--pr-ref-pr-number pr-descriptor)))
         (arguments `((owner . ,owner) (name . ,repo) (number . ,pull-number)))
         (raw-result-file-comments (ghub-query lgtm-github--get-pr-comments-query arguments :auth 'lgtm :synchronous t))
         (narrow-result-file-comments (lgtm-github--graphql-select raw-result-file-comments '((data . 0) (repository . 0) (pullRequest . 0) reviewThreads)))
         (file-comments (seq-map (lambda (node) (lgtm-github--parse-comment-thread file-manager node)) narrow-result-file-comments))
         (raw-result-top-level-comments (ghub-query lgtm-github--get-pr-top-level-comments-query arguments :auth 'lgtm :synchronous t))
         (narrow-result-top-level-comments (lgtm-github--graphql-select raw-result-top-level-comments '((data . 0) (repository . 0) (pullRequest . 0) comments)))
         (top-level-comments (seq-map (lambda (node) (lgtm-github--parse-top-level-comment-thread node)) narrow-result-top-level-comments)))
    (seq-concatenate 'list top-level-comments (seq-mapcat (lambda (x) x) file-comments))))

(defun lgtm-github--get-comment-revision (side)
  "Map the GitHub diff SIDE to an internal revision (base or current).

Note that some of the GraphQL APIs do not return the side.  When that is
the case (side is nil), we assume it is the current revision.  See
[ref:get-review-comments-query]."
  (pcase side
    ("LEFT" 'base)
    ("RIGHT" 'current)
    ((pred null) 'current)
    (_ (progn
         (warn "Unexpected comment side `%s'" side)
         nil))))

(defun lgtm-github--get-file-of-change (file-manager version path)
  "Given the PATH from a Github comment, map to the corresponding modified file.

This requires the VERSION (base or current) to determine which filename
to refer to in the case of a rename.

This uses the FILE-MANAGER to determine the file.  Returns nil with a warning
if no mapping can be found.

Because Github PRs are only against a single repository, this matching can
ignore the repository entirely."
  (let ((modified-files (lgtm--modified-file-manager-modified-files file-manager)))
    (seq-find (lambda (modified-file)
                (pcase version
                  ('base (let ((base-filename (lgtm--modified-file-base-filename modified-file))
                               (current-filename (lgtm--modified-file-current-filename modified-file)))
                           (equal path (if base-filename base-filename current-filename))))
                  ('current (equal path (lgtm--modified-file-current-filename modified-file)))
                  (_ (error "Invalid version type `%s'" version))))
                modified-files)))

(defun lgtm-github--parse-timestamp (s)
  "Parse a timestamp string S into a Lisp timestamp."
  (if s
      (encode-time (parse-time-string s))
      nil))

(defun lgtm-github--get-remote-conversations (file-manager repository pr-descriptor)
  "Fetch comments for the given PR-DESCRIPTOR from the REPOSITORY.

The FILE-MANAGER enables this to map the file name reported by
the server to the internal immutable changed file reference type."
  (lgtm-github--get-pr-comments file-manager repository pr-descriptor))

(defun lgtm-github--get-pending-review-comments (gh-username file-manager pr-info)
  "Get the comments attached to the pending review in PR-INFO.

The FILE-MANAGER is required to reconstruct valid `lgtm-comment`
objects.  The GH-USERNAME is used to filter and find the current pending
review.

We use the GraphQL API for this (instead of the REST API) because the
REST API only returns position information using the old (deprecated)
format of positions relative to diff hunks.  Instead of writing a parser
and interpreter for that format, we just use the GraphQL API, which lets
us select the sane position information directly.

However, this API doesn't return diff side information.  When the side
is nil, we just assume it is attached to the current review
state (instead of the base).  See [ref:get-review-comments-query]."
  (let* ((owner (lgtm-github--pr-info-owner pr-info))
         (repo (lgtm-github--pr-info-repository-name pr-info))
         (pull-number (lgtm-github--pr-info-number pr-info))
         (author gh-username)
         (states '["PENDING"])
         (variables `((owner . ,owner) (name . ,repo) (number . ,pull-number) (author . ,author) (states . ,states)))
         (raw-response (ghub-query lgtm-github--get-current-review-comments-query variables :auth 'lgtm :synchronous t))
         ;; We select the first (0th) review because there is exactly one pending review right now
         ;; (we know since we created it and limited the search to only pending reviews, and there
         ;; can only be one pending review per user).
         (narrowed-response (lgtm-github--graphql-select raw-response '((data . 0) (repository . 0) (pullRequest . 0) (reviews . 0) 0 comments)))
         (parsed-comments (seq-map (lambda (node) (lgtm-github--parse-review-comment file-manager node)) narrowed-response)))
    parsed-comments))

(defun lgtm-github--delete-pending-review (pr-info review-id)
  "Delete the pending REVIEW-ID for PR-INFO.

This is part of the protocol for adding a new review comment."
  (let* ((owner (lgtm-github--pr-info-owner pr-info))
         (repo (lgtm-github--pr-info-repository-name pr-info))
         (pull-number (lgtm-github--pr-info-number pr-info))
         (resource (format "/repos/%s/%s/pulls/%d/reviews/%s" owner repo pull-number review-id))
         (arguments '()))
    (ghub-request "DELETE" resource arguments :auth 'lgtm)))

(defun lgtm-github--create-review-comment (gh-username file-manager pr-info comment)
  "Create an unpublished COMMENT under the current review.

This uses the REPOSITORY and PR-ID to create the request.  The FILE
is required because the COMMENT only contains a ref.

The REVIEW-ID is the draft review to attach the comment to.

Returns the id of the comment."
  (let* ((body (lgtm-comment-content comment))
         (loc (lgtm-comment-location comment))
         (reply-to-id (lgtm-comment-reply-to-id comment)))
    (cond
     ((not loc) (let* ((owner (lgtm-github--pr-info-owner pr-info))
                       (repo-name (lgtm-github--pr-info-repository-name pr-info))
                       (pull-number (lgtm-github--pr-info-number pr-info))
                       (resource (format "/repos/%s/%s/issues/%s/comments" owner repo-name pull-number))
                       (arguments `((body . ,body)))
                       (response (ghub-post resource arguments :auth 'lgtm)))
                  (alist-get 'id response)))
     (reply-to-id (let* ((arguments `((body . ,body) (in_reply_to . ,reply-to-id)))
                         (owner (lgtm-github--pr-info-owner pr-info))
                         (repo-name (lgtm-github--pr-info-repository-name pr-info))
                         (pull-number (lgtm-github--pr-info-number pr-info))
                         (resource (format "/repos/%s/%s/pulls/%d/comments" owner repo-name pull-number)))
                    (let ((response (ghub-post resource arguments :auth 'lgtm)))
                      (alist-get 'id response))))
     (t (let* ((review-id (lgtm-github--get-or-create-draft-review gh-username pr-info))
               (current-pending-comments (lgtm-github--get-pending-review-comments gh-username file-manager pr-info)))
          (lgtm-github--delete-pending-review pr-info review-id)

          (condition-case github-error
              (let ((new-review-id (lgtm-github--create-new-review pr-info (cons comment current-pending-comments))))
                (setf (lgtm-github--pr-info-review-id pr-info) new-review-id)
                ;; Ideally we would look up the comment id here.  However, for unpublished comments
                ;; (all of these are unpublished), the ids are not stable.  It should not matter
                ;; very much since the user cannot publish a reply to any of these comments anyway,
                ;; so it shouldn't matter much.
                t)

            ;; If comment creation fails, try to recreate the review in a reasonable form without
            ;; the offending comment.  We can't tell if the operation will fail or not without
            ;; trying, so this is the best we can do.
            (ghub-http-error (let ((new-review-id (lgtm-github--create-new-review pr-info current-pending-comments)))
                               (setf (lgtm-github--pr-info-review-id pr-info) new-review-id)
                               (warn "Could not create comment %s: %s" comment github-error)
                               nil))))))))

(defun lgtm-github--get-existing-pending-review (gh-username pr-info)
  "Get the id of an existing pending review.

Requires the GH-USERNAME to filter reviews to only the current user.
Requires the PR-INFO to get the relevant reviews for the PR.

Returns nil if there is no pending PR."
  (let* ((owner (lgtm-github--pr-info-owner pr-info))
         (repo (lgtm-github--pr-info-repository-name pr-info))
         (pull-number (lgtm-github--pr-info-number pr-info))
         (resource (format "/repos/%s/%s/pulls/%d/reviews" owner repo pull-number))
         (arguments '())
         (response (ghub-get resource arguments :auth 'lgtm)))

    (let* ((is-pending-review-p (lambda (pr)
                                  (let-alist pr
                                    (and (equal gh-username .user.login) (equal "PENDING" .state)))))
           (existing-pending-pr (seq-find is-pending-review-p response)))

      (if existing-pending-pr
          (alist-get 'id existing-pending-pr)
        nil))))

(defun lgtm-github--comment-to-github-rest (comment)
  "Convert an internal COMMENT into the form required by the Github REST API."
  (let* ((body (lgtm-comment-content comment))
         (loc (lgtm-comment-location comment))
         (loc-vars (lgtm-github--get-comment-file loc)))
    (cons `(body . ,body) loc-vars)))

(defun lgtm-github--create-new-review (pr-info review-comments)
  "Create a new draft review for the PR implied by PR-INFO."
  (let* ((owner (lgtm-github--pr-info-owner pr-info))
         (repo-name (lgtm-github--pr-info-repository-name pr-info))
         (pull-number (lgtm-github--pr-info-number pr-info))
         (resource (format "/repos/%s/%s/pulls/%d/reviews" owner repo-name pull-number))
         ;; We make the comments array a vector so that when we create the structure:
         ;;
         ;; > `((comments . [...]))
         ;;
         ;; instead of:
         ;;
         ;; > `((comments (...)))
         ;;
         ;; as the latter will fail to encode into JSON.
         (translated-comments (seq-into (seq-map #'lgtm-github--comment-to-github-rest review-comments) 'vector))
         (arguments (if review-comments (list (cons 'comments translated-comments)) nil))
         (response (ghub-post resource arguments :auth 'lgtm)))
    (alist-get 'id response)))

(defun lgtm-github--get-or-create-draft-review (gh-username pr-info)
  "Get the id of the draft review for PR-INFO.

This function creates a draft review if none exists.  Note that the github
create review call will fail if there is an existing request.  To find an
existing review, we have to list existing reviews and find a pending one.

This requires the GH-USERNAME to ensure that any discovered PENDING PR
belongs to this user.

This uses a cached local copy of the review id if possible.  This could
break if the user deletes the review on the server side during the lgtm
session."
  (let ((cached-review-id (lgtm-github--pr-info-review-id pr-info)))
    (if cached-review-id
        cached-review-id
      (let* ((current-review-id (lgtm-github--get-existing-pending-review gh-username pr-info)))
        (if current-review-id
            (progn
              (setf (lgtm-github--pr-info-review-id pr-info) current-review-id)
              current-review-id)
          ;; If we have to create a new review, it has no comments
          (let ((new-review-id (lgtm-github--create-new-review pr-info '())))
            (setf (lgtm-github--pr-info-review-id pr-info) new-review-id)
            new-review-id))))))

(defun lgtm-github--submit-review (gh-username pr-info)
  "Submit the given review against the given PR.

The PR-INFO encodes the details that uniquely identify the PR."
  (let ((review-id (lgtm-github--get-or-create-draft-review gh-username pr-info)))
    (if review-id
        (let* ((owner (lgtm-github--pr-info-owner pr-info))
               (repo-name (lgtm-github--pr-info-repository-name pr-info))
               (pull-number (lgtm-github--pr-info-number pr-info))
               (resource (format "/repos/%s/%s/pulls/%d/reviews/%s/events" owner repo-name pull-number review-id))
               (arguments '((event . "COMMENT") (body . ""))))
          (ghub-post resource arguments :auth 'lgtm)
          nil)
      (warn "No review initiated"))))

(defun lgtm-github--approve-pr (gh-username pr-info)
  "Approve the PR and publish draft comments.

The PR-INFO encodes the details that uniquely identify the PR."
  (let ((review-id (lgtm-github--get-or-create-draft-review gh-username pr-info)))
    (if review-id
        (let* ((owner (lgtm-github--pr-info-owner pr-info))
               (repo-name (lgtm-github--pr-info-repository-name pr-info))
               (pull-number (lgtm-github--pr-info-number pr-info))
               (resource (format "/repos/%s/%s/pulls/%d/reviews/%s/events" owner repo-name pull-number review-id))
               (arguments '((event . "APPROVE") (body . ""))))
          (ghub-post resource arguments :auth 'lgtm)
          nil)
      (warn "No review initiated"))))

(defun lgtm-github--get-comment-file (loc)
  "Get the position and file path of the a comment given the comment LOC.

Returns a alist that matches the query constructors."
  (let* ((modified-file (lgtm-comment-location-file loc))
         (start-line (lgtm-comment-location-start-line loc))
         (line (lgtm-comment-location-end-line loc))
         (path (lgtm--path-of-file-at-version (lgtm-comment-location-version loc) modified-file)))
    (pcase (lgtm-comment-location-version loc)
      ('base `((path . ,path) (start_line . ,start-line) (line . ,line) (side . "LEFT") (start_side . "LEFT")))
      ('current `((path . ,path) (start_line . ,start-line) (line . ,line) (side . "RIGHT") (start_side . "RIGHT")))
      (_ (error "Invalid version for file location %s" loc)))))

(defun lgtm-github--make-config (shutdown-hook)
  "Create a lgtm config for Github repositories/PRs.

The SHUTDOWN-HOOK is passed to the configuration to be called when
LGTM exits."
  (let* ((current-git-commit (lgtm-github--get-current-hash))
         (username (lgtm-github--get-github-username))
         (repository (lgtm-github--get-repository))
         (prs (lgtm-github--get-prs))
         (this-pr-id (seq-find (lambda (pr) (equal current-git-commit (lgtm-github--pr-ref-hash pr))) prs)))
    ;; Note that repository and this-pr-id are just bootstrapping data.
    ;;
    ;; Ideally all of the functions doing real work should just take pr-info (of type lgtm-github--pr-info)
    (message "Creating a review configuration for repository %s/%s and PR ID = %s" username repository this-pr-id)
    (if this-pr-id
        (let* ((pr-info (lgtm-github--get-pr-info repository this-pr-id))
               (base-revision (lgtm-github--pr-info-base-ref pr-info))
               (commits (lgtm--compute-change-commits default-directory base-revision))
               (review-state-backend (if (and (fboundp 'sqlite-available-p) (sqlite-available-p) lgtm-database-file)
                                         (lgtm--make-sqlite-review-state-backend lgtm-database-file)
                                       (lgtm--make-no-op-review-state-backend)))
               (git-repo (make-lgtm-repository :path default-directory
                                               :name (format "%s/%s" (lgtm-github--repository-owner repository) (lgtm-github--repository-repo repository))
                                               :commits commits
                                               :base-revision base-revision)))
          (make-lgtm-configuration
           :user username
           :changeset-id (lgtm-github--pr-info-id pr-info)
           :repositories (list git-repo)
           :author (lgtm-github--pr-info-author-login pr-info)
           :created-at (lgtm-github--pr-info-created-at pr-info)
           :changeset-url (lgtm-github--pr-info-url pr-info)
           :changeset-title (lgtm-github--pr-info-title pr-info)
           :changeset-description (lgtm-github--pr-info-body pr-info)
           :state (lgtm-github--pr-info-state pr-info)
           :review-state-backend review-state-backend
           :get-remote-conversations-function (lambda (file-manager) (lgtm-github--get-remote-conversations file-manager repository this-pr-id))
           :create-review-comment-function (lambda (file-manager comment) (lgtm-github--create-review-comment username file-manager pr-info comment))
           :submit-review-function (lambda () (lgtm-github--submit-review username pr-info))
           :approve-review-function (lambda () (lgtm-github--approve-pr username pr-info))
           :shutdown-hook shutdown-hook))
      (error "Could not find a PR corresponding to `%s'" current-git-commit))))

(defun lgtm-github--pr-tempdir-name (pr)
  "Create a temporary dir name for the given PR."
  (let ((repo (lgtm-github--repo-pr-repository pr)))
    (format "lgtm-%s-%s-%s" (lgtm-github--repository-owner repo)
            (lgtm-github--repository-repo repo)
            (lgtm-github--repo-pr-pr-num pr))))

(defun lgtm-github--pr-clone-url (pr)
  "Construct a URL to clone the repository for the given PR."
  (let ((repo (lgtm-github--repo-pr-repository pr)))
    (format "https://github.com/%s/%s" (lgtm-github--repository-owner repo)
            (lgtm-github--repository-repo repo))))

(defun lgtm-github--pr-ref (pr)
  "Return the ref of the PR in the remote repository."
  (format "pull/%s/head" (lgtm-github--repo-pr-pr-num pr)))

;;;###autoload
(defun lgtm-github-review-pr (url)
  "Pull the PR from the given URL and review it."
  (interactive "MURL: ")
  (let ((pr (lgtm-github--parse-pr-url url)))
    (if pr
        (let* ((temp-dir (make-temp-file (lgtm-github--pr-tempdir-name pr) t))
               (clone-url (lgtm-github--pr-clone-url pr))
               (ref (lgtm-github--pr-ref pr))
               (shutdown-hook (lambda () (delete-directory temp-dir t))))
          (let ((default-directory temp-dir))
            (call-process "git" nil nil nil "clone" clone-url ".")
            (call-process "git" nil nil nil "fetch" "origin" (format "%s:%s" ref ref))
            (call-process "git" nil nil nil "switch" ref)
            (let ((conf (lgtm-github--make-config shutdown-hook)))
              (lgtm-start conf))))
      (error "Unsupported PR URL %s" url))))

(provide 'lgtm-github)

;;; lgtm-github.el ends here
