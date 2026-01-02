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

(ert-deftest test-indexing-empty-comments-list-is-empty ()
  (let ((locs (lgtm--index-comments '())))
    (should (equal locs '()))))

(ert-deftest test-indexing-singleton-list ()
  (let* ((c0 (make-lgtm-comment :backend-data "backend-id"
                               :ref "ref"
                               :location (make-test-location 1)
                               :created-timestamp 5
                               :parent nil
                               :content "content"))
         (locs (lgtm--index-comments (list c0))))
    (should (equal (length locs) 1))
    (should (not (equal (assoc location1 locs) nil)))
    (should (equal (assoc 10 locs) nil))))

(ert-deftest test-index-comments-at-different-locs ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 1)
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 2)
                                :created-timestamp 5
                                :parent nil
                                :content "content2"))
         (locs (lgtm--index-comments (list c1 c2))))
    (should (equal (length locs) 2))
    (should-not (equal (assoc location1 locs) nil))
    (should-not (equal (assoc location2 locs) nil))
    (should (equal (assoc 10 locs) nil))

    (let* ((pos-list-for-loc-1 (alist-get location1 locs nil nil 'equal))
           (pcomment1 (elt (elt pos-list-for-loc-1 0) 0)))
      (should (equal (length pos-list-for-loc-1) 1))
      (should (equal (lgtm--positioned-comment-indent pcomment1) 0))
      (should (equal (lgtm--positioned-comment-comment pcomment1) c1)))

    (let* ((pos-list-for-loc-2 (alist-get location2 locs nil nil 'equal))
           (pcomment2 (elt (elt pos-list-for-loc-2 0) 0)))
      (should (equal (length pos-list-for-loc-2) 1))
      (should (equal (lgtm--positioned-comment-indent pcomment2) 0))
      (should (equal (lgtm--positioned-comment-comment pcomment2) c2)))))

(ert-deftest test-index-two-comments-at-same-loc ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 1)
                                :created-timestamp 5
                                :parent nil
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 1)
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (locs (lgtm--index-comments (list c1 c2))))

    (should (equal (length locs) 1))

    (let ((loc-1-comments (alist-get location1 locs nil nil 'equal)))
      (should (equal (length loc-1-comments) 2))
      ;; These are two independent threads, each with a single top-level element
      (let ((pcomment1 (elt (elt loc-1-comments 0) 0))
            (pcomment2 (elt (elt loc-1-comments 1) 0)))
        (should (equal (lgtm--positioned-comment-indent pcomment1) 0))
        (should (equal (lgtm--positioned-comment-indent pcomment2) 0))
        ;; c1 should be first because it has a lower timestamp
        (should (equal (lgtm--positioned-comment-comment pcomment1) c1))))

    (let ((loc-2-comments (alist-get location2 locs nil nil 'equal)))
      (should (equal loc-2-comments '())))))

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
         (locs (lgtm--index-comments (list c1 c2))))

    (should (equal (length locs) 1))

    (let ((thread (elt (alist-get location1 locs nil nil 'equal) 0)))

      (should (equal (length thread) 2))

      (let ((root-comment (elt thread 0))
            (reply-comment (elt thread 1)))
        (should (equal (lgtm--positioned-comment-indent root-comment) 0))
        (should (equal (lgtm--positioned-comment-comment root-comment) c2))

        (should (equal (lgtm--positioned-comment-indent reply-comment) 1))
        (should (equal (lgtm--positioned-comment-comment reply-comment) c1))))))

(ert-deftest test-reply-structure-supercedes-location ()
  (let* ((c1 (make-lgtm-comment :backend-data "backend-id-1"
                                :ref "ref-1"
                                :location (make-test-location 10)
                                :created-timestamp 5
                                :parent "backend-id-2"
                                :content "content1"))
         (c2 (make-lgtm-comment :backend-data "backend-id-2"
                                :ref "ref-2"
                                :location (make-test-location 1)
                                :created-timestamp 6
                                :parent nil
                                :content "content2"))
         (locs (lgtm--index-comments (list c1 c2))))

    (should (equal (length locs) 1))

    (let ((thread (elt (alist-get location1 locs nil nil 'equal) 0)))

      (should (equal (length thread) 2))

      (let ((root-comment (elt thread 0))
            (reply-comment (elt thread 1)))
        (should (equal (lgtm--positioned-comment-indent root-comment) 0))
        (should (equal (lgtm--positioned-comment-comment root-comment) c2))

        (should (equal (lgtm--positioned-comment-indent reply-comment) 1))
        (should (equal (lgtm--positioned-comment-comment reply-comment) c1))))))

(provide 'test-comment-index)

;;; test-comment-index.el ends here
