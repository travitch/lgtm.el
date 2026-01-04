;; test-github-utils.el -*- lexical-binding: t; -*-
;;
;; This file has tests for the Github adapter

(require 'lgtm-github)

;;; Code:

(ert-deftest test-empty-data ()
  (should (equal (lgtm-github--graphql-select nil '(foo bar)) nil)))

(ert-deftest test- ()
  (let ((data '(root (body)))
        (path '((root . 0)))
        (expected '(body)))
    (should (equal (lgtm-github--graphql-select data path) expected))))

(ert-deftest test-mutation-parsing1 ()
  (let ((data '(data (addPullRequestReview (pullRequestReview (id . "PRR_kwDONpeWls7YEzTP")))))
        (path '((data . 0) (addPullRequestReview . 0) (pullRequestReview . 0) id))
        (expected "PRR_kwDONpeWls7YEzTP"))
    (should (equal (lgtm-github--graphql-select data path) expected))))

(provide 'test-github-utils)

;;; test-github-utils.el ends here
