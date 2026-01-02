;; test-git-parsing.el -*- lexical-binding: t; -*-
;;
;; This file has tests for various parsers for git command output.

(require 'lgtm-core)

;;; Code:

(ert-deftest test-error-on-parsing-invalid-modification-type ()
  (should-error (lgtm--parse-modified-type "X")))

(ert-deftest test-parse-m-modification ()
  (should (equal (lgtm--parse-modified-type "M") 'modified)))

(ert-deftest test-parse-m-modification-with-suffix ()
  (should (equal (lgtm--parse-modified-type "M100") 'modified)))

(ert-deftest test-parse-a-modification ()
  (should (equal (lgtm--parse-modified-type "A") 'added)))

(ert-deftest test-parse-d-modification ()
  (should (equal (lgtm--parse-modified-type "D") 'deleted)))

(ert-deftest test-parse-t-modification ()
  (should (equal (lgtm--parse-modified-type "T") 'typechange)))

(ert-deftest test-parse-r-modification ()
  (should (equal (lgtm--parse-modified-type "R") 'renamed)))

(ert-deftest test-parse-c-modification ()
  (should (equal (lgtm--parse-modified-type "C") 'copied)))

(ert-deftest test-git-short-commit-log-parsing ()
  (should (equal (lgtm--parse-git-short-commit "abcd12345 Commit message") '("abcd12345" . "Commit message"))))

(ert-deftest test-git-short-commit-malformed-parse-fails ()
  (should-error (lgtm--parse-git-short-commit "zzz")))

(provide 'test-git-parsing)

;;; test-git-parsing.el ends here
