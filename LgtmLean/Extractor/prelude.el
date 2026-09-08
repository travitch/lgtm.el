(defun lgtm--hash-map-to-list (m)
  "Convert a hash table M to a list of two-element lists."
  (let ((res '()))
    (maphash (lambda (key value) (setf res (cons (list key value) res))) m)
    res))

(defun lgtm--hash-map-map (func m)
  "Map FUNC over M to produce a new map.

The function is called with two arguments: the keys and values from M."
  (let ((res (make-hash-table)))
    (maphash (lambda (key value) (puthash key (funcall func value) res)) m)
    res))

(defun lgtm--hash-map-insert (key value m)
  "Insert KEY mapped to VALUE in M.

This does not mutate the original map."
  (let ((res (copy-hash-table m)))
    (puthash key value res)
    res))

;; Tuples (including pairs) are represented as lists in the translation

(defun lgtm--pair-fst (p)
  "Select the first element of a tuple P."
  (elt p 0))

(defun lgtm--pair-snd (p)
  "Select the second element of a tuple P."
  (elt p 1))
