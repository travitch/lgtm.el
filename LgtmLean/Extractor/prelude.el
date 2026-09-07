(defun lgtm--hash-map-to-list (m)
  "Convert a hash table M to a list of two-element lists."
  (let ((res '()))
    (maphash (lambda (key value) (setf res (cons (list key value) res))) m)
    res))

