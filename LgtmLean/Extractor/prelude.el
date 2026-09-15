(defun lgtm--hash-map-to-list (m)
  "Convert a hash table M to a list of two-element lists."
  (let ((res '()))
    (maphash (lambda (key value) (setf res (cons (vector key value) res))) m)
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

(defun lgtm--list-idx-of (elt lst)
  "Find the index of ELT in LST.

Returns the length of the list of no element is equal to ELT."
  (let ((idx (seq-position lst elt)))
    (if idx idx (length lst))))

(defun lgtm--list-find-idx (p lst)
  "Find the index of the first item in LST that matches P.

Returns nil if none is found."
  (let ((item (seq-find (lambda (item) (funcall p (elt item 0))) (seq-map-indexed #'list lst))))
    (if item (elt item 1) nil)))

(defun lgtm--list-any (p lst)
  "Whether any element of LST satisfies P.

Unlike `seq-some', this answers with t rather than with P's own return value."
  (if (seq-some p lst) t nil))

(defun lgtm--list-nodup-p (eq-fn lst)
  "Whether no two elements of LST are equal according to EQ-FN."
  (= (length lst) (length (seq-uniq lst eq-fn))))

(defun lgtm--option-decidable-eq (eq-fn a b)
  "Whether option-represented values A and B (nil for none) are equal.

Compares the payloads via EQ-FN when both are present; otherwise equal only if both are absent."
  (if (and a b) (funcall eq-fn a b) (not (or a b))))

;; Tuples (including pairs) are represented as vectors in the translation

(defun lgtm--pair-fst (p)
  "Select the first element of a tuple P."
  (elt p 0))

(defun lgtm--pair-snd (p)
  "Select the second element of a tuple P."
  (elt p 1))
