;; test-comment-index.el -*- lexical-binding: t; -*-

(require 'lgtm-core)

;;; Code:

(defun make-test-location (line)
  (make-lgtm-comment-location :start-line line))

;; These are a few location definitions to make specifying tests easier.
;;
;; The test cases specify their inputs without using these to ensure that the location objects are
;; not pointer equal, which helps test that the implementation is not accidentally using pointer
;; equality.
(defconst location1 (make-test-location 1))
(defconst location2 (make-test-location 2))

(defun construct-test-threads (comments)
  "Construct a thread structure for COMMENTS."
  (let ((threads (make-lgtm--comment-threads)))
    (lgtm--assemble-comment-trees threads comments)
    threads))

(defun expect-comment-in-thread-at (thread path c)
  "Expect to find C by following PATH in THREAD.

The path is a list of child indices to traverse."
  (if (null path)
      (progn
        (cl-assert (equal c (lgtm--tree-value thread)) t "Expected to find target comment")
        thread)
    (expect-comment-in-thread-at (seq-elt (lgtm--tree-children thread) (car path)) (cdr path) c)))

(defun expect-comment-at (located-threads location thread-num path c)
  "Assert that C exists in LOCATED-THREADS at LOCATION, at THREAD-NUM at that location, following PATH through the thread."
  (cl-assert located-threads t "Expect located threads to be calculated")
  (cl-assert location t "Expect a location to be specified")
  (cl-assert thread-num t "Expect a thread number index")
  (cl-assert c t "Expect a target comment")
  (let ((threads-at-loc (alist-get location located-threads)))
    (cl-assert threads-at-loc t (format "Expect at least one thread at %s" location))
    (cl-assert (< thread-num (length threads-at-loc)) t (format "Expect there to be at least %d threads" thread-num))
    (let ((thread (seq-elt threads-at-loc thread-num)))
      (cl-assert thread t "Expect a thread")
      (expect-comment-in-thread-at thread path c))))


(ert-deftest test-indexing-empty-comments-list-is-empty ()
  (let* ((threads (construct-test-threads '())))
    (should (equal '() (lgtm--comment-threads-alist threads)))
    (should (equal '() (lgtm--comment-threads-ordered threads)))
    (should (equal 0 (lgtm--comment-threads-comment-count threads)))))

(ert-deftest test-indexing-singleton-list ()
  (let* ((c0 (make-lgtm-comment :backend-data "backend-id"
                               :ref "ref"
                               :location location1
                               :created-timestamp 5
                               :parent nil
                               :content "content"))
         (threads-index (construct-test-threads (list c0)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index))
         (comment-trees (lgtm--comment-threads-ordered threads-index)))
    (should (equal (length comment-trees-alist) 1))
    (should (equal (length comment-trees) 1))
    (expect-comment-at comment-trees-alist 1 0 '() c0)))

(ert-deftest test-index-comments-at-different-locs ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))
    (should (equal (length comment-trees-alist) 2))
    (expect-comment-at comment-trees-alist 1 0 '() c1)
    (expect-comment-at comment-trees-alist 2 0 '() c2)))

(ert-deftest test-index-two-comments-at-same-loc ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location1
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))

    ;; c1 should be first in the list because it has a lower timestamp
    (expect-comment-at comment-trees-alist 1 0 '() c1)
    (expect-comment-at comment-trees-alist 1 1 '() c2)
    (should-error (expect-comment-at comment-trees-alist 2 0 '() c1))))

;; Testing what happens when the server returns the comments with the newer timestamp first
(ert-deftest test-index-two-comments-at-same-loc-reversed ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 6
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))

    ;; c2 should be first in the list because it has a lower timestamp
    (expect-comment-at comment-trees-alist 1 1 '() c1)
    (expect-comment-at comment-trees-alist 1 0 '() c2)
    (should-error (expect-comment-at comment-trees-alist 2 0 '() c1))))

(ert-deftest test-index-two-comment-thread ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 1)
                                :created-timestamp 5
                                :parent "backend-id-2"
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 1)
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))

    (expect-comment-at comment-trees-alist 1 0 '() c2)
    (expect-comment-at comment-trees-alist 1 0 '(0) c1)))

(ert-deftest test-reply-structure-supercedes-location ()
  ;; The location on c1 is malformed since only the parent matters
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 10)
                                :created-timestamp 5
                                :parent "backend-id-2"
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location1
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))
    (expect-comment-at comment-trees-alist 1 0 '() c2)
    (expect-comment-at comment-trees-alist 1 0 '(0) c1)))

(ert-deftest test-insert-comment-at-new-loc ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location (make-test-location 3)
                                :created-timestamp 10
                                :parent nil
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))
    (should (equal (length comment-trees-alist) 3))
    (expect-comment-at comment-trees-alist 1 0 '() c1)
    (expect-comment-at comment-trees-alist 2 0 '() c2)
    (expect-comment-at comment-trees-alist 3 0 '() c3)))

;; In this test c3 is the earliest comment in the file; it shouldn't matter.
(ert-deftest test-insert-comment-at-new-loc-before-others ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location (make-test-location 0)
                                :created-timestamp 10
                                :parent nil
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))
    (should (equal (length comment-trees-alist) 3))
    (expect-comment-at comment-trees-alist 1 0 '() c1)
    (expect-comment-at comment-trees-alist 2 0 '() c2)
    (expect-comment-at comment-trees-alist 0 0 '() c3)))

;; c3 should come after c1 at location 1
(ert-deftest test-insert-comment-at-existing-loc-after-original ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location location1
                                :created-timestamp 10
                                :parent nil
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))
    (should (equal (length comment-trees-alist) 2))
    (expect-comment-at comment-trees-alist 1 0 '() c1)
    (expect-comment-at comment-trees-alist 2 0 '() c2)
    (expect-comment-at comment-trees-alist 1 1 '() c3)))

;; c3 should come before c1 at location 1
(ert-deftest test-insert-comment-at-existing-loc-before-original ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location location1
                                :created-timestamp 1
                                :parent nil
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))
    (should (equal (length comment-trees-alist) 2))
    (expect-comment-at comment-trees-alist 1 1 '() c1)
    (expect-comment-at comment-trees-alist 2 0 '() c2)
    (expect-comment-at comment-trees-alist 1 0 '() c3)))

(ert-deftest test-insert-comment-in-two-comment-thread-after ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 1)
                                :created-timestamp 5
                                :parent "backend-id-2"
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 1)
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location location1
                                :created-timestamp 10
                                :parent "backend-id-2"
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))

    (expect-comment-at comment-trees-alist 1 0 '() c2)
    (expect-comment-at comment-trees-alist 1 0 '(0) c1)
    (expect-comment-at comment-trees-alist 1 0 '(1) c3)))

(ert-deftest test-insert-comment-in-two-comment-thread-before ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 1)
                                :created-timestamp 5
                                :parent "backend-id-2"
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 1)
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (c3 (make-lgtm-comment :backend-data "backend-id-3"
                                :ref "ref-3"
                                :location location1
                                :created-timestamp 1
                                :parent "backend-id-2"
                                :content "content3"))
         (threads-index (construct-test-threads (list c1 c2)))
         (_ (lgtm--add-comment-to-thread threads-index c3))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index)))

    (should (equal (length comment-trees-alist) 1))

    (expect-comment-at comment-trees-alist 1 0 '() c2)
    (expect-comment-at comment-trees-alist 1 0 '(1) c1)
    (expect-comment-at comment-trees-alist 1 0 '(0) c3)))

(ert-deftest test-next-comment-no-start-selection ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (initial-selection nil))

    (let ((next-selection (lgtm--selected-comment-next-thread threads-index 'base initial-selection)))
      (should (equal (lgtm-comment-ref (lgtm--tree-value (lgtm--selected-comment-thread next-selection))) "ref-1")))))

(ert-deftest test-next-comment-with-first-selected ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index))
         (initial-selection (make-lgtm--selected-comment :version 'base :thread (seq-elt (alist-get 1 comment-trees-alist) 0))))

    (let ((next-selection (lgtm--selected-comment-next-thread threads-index 'base initial-selection)))
      (should (equal (lgtm-comment-ref (lgtm--tree-value (lgtm--selected-comment-thread next-selection))) "ref-2")))))

(ert-deftest test-next-comment-with-last-selected-is-id ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index))
         (initial-selection (make-lgtm--selected-comment :version 'base :thread (seq-elt (alist-get 2 comment-trees-alist) 0))))

    (let ((next-selection (lgtm--selected-comment-next-thread threads-index 'base initial-selection)))
      (should (equal (lgtm-comment-ref (lgtm--tree-value (lgtm--selected-comment-thread next-selection))) "ref-2")))))

(ert-deftest test-next-comment-with-other-buffer ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location location1
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location location2
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (threads-index (construct-test-threads (list c1 c2)))
         (comment-trees-alist (lgtm--comment-threads-alist threads-index))
         (initial-selection (make-lgtm--selected-comment :version 'base :thread (seq-elt (alist-get 2 comment-trees-alist) 0))))

    (let ((next-selection (lgtm--selected-comment-next-thread threads-index 'current initial-selection)))
      (should (equal (lgtm-comment-ref (lgtm--tree-value (lgtm--selected-comment-thread next-selection))) "ref-1")))))


(provide 'test-comment-index)

;;; test-comment-index.el ends here
