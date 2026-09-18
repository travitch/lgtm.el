;;; test-harness.el --- Runner for the extracted-elisp tests -*- lexical-binding: t; -*-

;;; Commentary:

;; Loaded by the `test' executable (`Test.lean', which `lake test' runs) into a
;; fresh `emacs -Q --batch', ahead of the freshly generated `lgtm-lean-core.el'
;; and a generated file of checks.
;;
;; Each check pairs an elisp expression -- a call into the extracted code -- with
;; the elisp source of the value the corresponding Lean function produced when
;; `Test.lean' ran it.  This file only provides the machinery to run such a pair
;; and report on it; the checks themselves are written in `Test.lean'.

;;; Code:

(require 'cl-lib)
(require 'seq)

(defvar lgtm-test--passed 0
  "Number of checks that have passed so far.")

(defvar lgtm-test--failed 0
  "Number of checks that have failed so far.")

(defconst lgtm-test--absent (make-symbol "lgtm-test--absent")
  "Sentinel returned by `gethash' for a key that is missing.
Distinct (under `eq') from every value a check can produce.")

(defun lgtm-test--hash-table (entries)
  "Build the extracted representation of a Lean `Std.HashMap' from ENTRIES.
ENTRIES is a list of two-element vectors [KEY VALUE], matching how the
extraction represents a pair.  The table is `equal'-tested because Lean
compares keys by value: two `CommentRef's with the same id are the same key,
and they are separate records here."
  (let ((table (make-hash-table :test #'equal)))
    (dolist (entry entries table)
      (puthash (elt entry 0) (elt entry 1) table))))

(defun lgtm-test--seq-equal (a b)
  "Whether the elements of equal-length sequences A and B are `lgtm-test--equal'."
  (catch 'lgtm-test--done
    (dotimes (i (length a) t)
      (unless (lgtm-test--equal (aref a i) (aref b i))
        (throw 'lgtm-test--done nil)))))

(defun lgtm-test--equal (a b)
  "Whether A and B are the same value, structurally.

This is `equal' with two adjustments, both about hash tables:

`equal' compares hash tables by identity, so it has to be taught to descend
into them -- including when they are nested inside a record, as the maps in a
`lgtm--comment-threads' are.

Lean's `Std.HashMap' and Emacs' `maphash' do not agree on iteration order, so
tables are compared as unordered key/value sets rather than element-wise."
  (cond
   ((and (hash-table-p a) (hash-table-p b))
    (and (= (hash-table-count a) (hash-table-count b))
         (catch 'lgtm-test--done
           (maphash (lambda (key value)
                      (unless (lgtm-test--equal value (gethash key b lgtm-test--absent))
                        (throw 'lgtm-test--done nil)))
                    a)
           t)))
   ((and (consp a) (consp b))
    (and (lgtm-test--equal (car a) (car b))
         (lgtm-test--equal (cdr a) (cdr b))))
   ;; Records (`cl-defstruct' values, i.e. Lean structures) and vectors (Lean
   ;; inductive constructors and tuples) are deliberately kept apart: a record
   ;; is never `equal' to a vector with the same contents, and the translation
   ;; relies on that distinction.
   ((and (recordp a) (recordp b))
    (and (= (length a) (length b)) (lgtm-test--seq-equal a b)))
   ((and (vectorp a) (vectorp b))
    (and (= (length a) (length b)) (lgtm-test--seq-equal a b)))
   ((or (hash-table-p a) (hash-table-p b)
        (recordp a) (recordp b)
        (vectorp a) (vectorp b)
        (consp a) (consp b))
    nil)
   (t (equal a b))))

(defun lgtm-test--format (value)
  "Render VALUE for a failure report."
  (let ((print-length 200)
        (print-level 20))
    (format "%S" value)))

(defun lgtm-test--check (index name expected-thunk actual-thunk)
  "Run one check, reporting on stdout and recording the outcome.

INDEX and NAME identify the check.  EXPECTED-THUNK returns the value computed
by Lean, and ACTUAL-THUNK calls the extracted elisp.  Both are thunks so that
an error raised while building either one is reported as a single failing
check rather than aborting the whole run."
  (condition-case err
      (let* ((expected (funcall expected-thunk))
             (actual (funcall actual-thunk)))
        (if (lgtm-test--equal expected actual)
            (setq lgtm-test--passed (1+ lgtm-test--passed))
          (setq lgtm-test--failed (1+ lgtm-test--failed))
          (princ (format "FAIL [%d] %s\n  expected (Lean):  %s\n  actual (elisp):   %s\n"
                         index name
                         (lgtm-test--format expected)
                         (lgtm-test--format actual)))))
    (error
     (setq lgtm-test--failed (1+ lgtm-test--failed))
     (princ (format "ERROR [%d] %s\n  %s\n" index name (error-message-string err))))))

(defun lgtm-test--finish ()
  "Report the totals and exit, non-zero if any check failed."
  (princ (format "%d passed, %d failed\n" lgtm-test--passed lgtm-test--failed))
  (kill-emacs (if (> lgtm-test--failed 0) 1 0)))

(provide 'test-harness)
;;; test-harness.el ends here
