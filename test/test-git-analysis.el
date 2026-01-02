;; test-git-analysis.el -*- lexical-binding: t; -*-
;;
;; This file has tests for git analysis infrastructure functions

(require 'lgtm-core)

;;; Code:

;; Define a few test repository histories as inputs

(defconst lgtm--test-repository1-name "repository1")
(defconst lgtm--test-repository1-path "/repository1")

(defconst lgtm--test-repository1-history
  '(
    ("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests")
    ("875c2cb3de236703a6f15424d54ea9cfc11bc8e7" . "Add a test harness")
    ("fdd5f5937463b7f39aeae502248901ec034647d1" . "Split some core functions with minimal dependencies into a separate module")
    ("c59c1bb80d75fbffb51bbfb57124adf19957634f" . "Add comment selection")))

(defconst lgtm--test-repository2-name "repository2")
(defconst lgtm--test-repository2-path "/repository2")

(defconst lgtm--test-repository2-history
  '(
    ("b23450a2084757c25a048df8f597f07b4a49eea6" . "Add a slot to track the currently-selected conversation in each file")
    ("93e7d58699670874f2bd1f55142f7cb20f21af50" . "Use an assertion")
    ("2f97be8b845133ea7622eafc471353cec6ca3e29" . "Start a github adapter")))

(defconst lgtm--test-repository3-name "repository3")

(defconst lgtm--test-repository3-history
  '(
    ("3d6df6942557da544b0ad3638309d2374ee7dd51" . "Fix more comment formatting")
    ("5ecd923587ef01df106fc1e0c019f49d5b7f3820" . "Fix timestamp parsing")
    ("6183cbb6b0006e15d6f8bd557fbc6cefac825099" . "Fetch comments from github")))


(ert-deftest test-parse-empty-repository-and-commit-list ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories '() '())))
    (should (equal repositories '()))))

;; These do produce warnings, as desired

(ert-deftest test-parse-empty-repository-with-commit-list ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories '() '("6183cbb6b0006e15d6f8bd557fbc6cefac825099"))))
    (should (equal repositories '()))))

(ert-deftest test-parse-empty-commit-list-with-repository ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository1-path . ,lgtm--test-repository1-history)) '())))
    (should (equal repositories '()))))

(ert-deftest test-one-commit-in-one-repository ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository1-path . ,lgtm--test-repository1-history))
                                                                    '("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5")))
        (expected (make-lgtm-repository :base-revision "875c2cb3de236703a6f15424d54ea9cfc11bc8e7"
                                        :name lgtm--test-repository1-name
                                        :commits '(("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests"))
                                        :path lgtm--test-repository1-path)))
    (should (equal repositories (list expected)))))

(ert-deftest test-two-commits-in-one-repository ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository1-path . ,lgtm--test-repository1-history))
                                                                    '("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" "875c2cb3de236703a6f15424d54ea9cfc11bc8e7")))
        (expected (make-lgtm-repository :base-revision "fdd5f5937463b7f39aeae502248901ec034647d1"
                                        :name lgtm--test-repository1-name
                                        :commits '(("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests")
                                                   ("875c2cb3de236703a6f15424d54ea9cfc11bc8e7" . "Add a test harness"))
                                        :path lgtm--test-repository1-path)))
    (should (equal repositories (list expected)))))

(ert-deftest test-two-commits-in-one-repository-target-order-swapped ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository1-path . ,lgtm--test-repository1-history))
                                                                    '("875c2cb3de236703a6f15424d54ea9cfc11bc8e7" "d73b0a1aaee3da752f4ead53ab7512408ed2bbd5")))
        (expected (make-lgtm-repository :base-revision "fdd5f5937463b7f39aeae502248901ec034647d1"
                                        :name lgtm--test-repository1-name
                                        :commits '(("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests")
                                                   ("875c2cb3de236703a6f15424d54ea9cfc11bc8e7" . "Add a test harness"))
                                        :path lgtm--test-repository1-path)))
    (should (equal repositories (list expected)))))


(ert-deftest test-two-commits-in-two-repositories ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository1-path . ,lgtm--test-repository1-history)
                                                                      (,lgtm--test-repository2-path . ,lgtm--test-repository2-history))
                                                                    '("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" "b23450a2084757c25a048df8f597f07b4a49eea6")))
        (expected1 (make-lgtm-repository :base-revision "875c2cb3de236703a6f15424d54ea9cfc11bc8e7"
                                         :name lgtm--test-repository1-name
                                         :commits '(("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests"))
                                         :path lgtm--test-repository1-path))
        (expected2 (make-lgtm-repository :base-revision "93e7d58699670874f2bd1f55142f7cb20f21af50"
                                         :name lgtm--test-repository2-name
                                         :path lgtm--test-repository2-path
                                         :commits '(("b23450a2084757c25a048df8f597f07b4a49eea6". "Add a slot to track the currently-selected conversation in each file")))))
    (should (equal repositories (list expected1 expected2)))))

(ert-deftest test-two-commits-in-two-repositories-reverse-input ()
  (let ((repositories (lgtm--assign-commits-to-repository-histories `((,lgtm--test-repository2-path . ,lgtm--test-repository2-history)
                                                                      (,lgtm--test-repository1-path . ,lgtm--test-repository1-history))
                                                                    '("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" "b23450a2084757c25a048df8f597f07b4a49eea6")))
        (expected1 (make-lgtm-repository :base-revision "875c2cb3de236703a6f15424d54ea9cfc11bc8e7"
                                         :name lgtm--test-repository1-name
                                         :commits '(("d73b0a1aaee3da752f4ead53ab7512408ed2bbd5" . "Add more tests"))
                                         :path lgtm--test-repository1-path))
        (expected2 (make-lgtm-repository :base-revision "93e7d58699670874f2bd1f55142f7cb20f21af50"
                                         :name lgtm--test-repository2-name
                                         :path lgtm--test-repository2-path
                                         :commits '(("b23450a2084757c25a048df8f597f07b4a49eea6" . "Add a slot to track the currently-selected conversation in each file")))))
    (should (equal repositories (list expected1 expected2)))))


(provide 'test-git-analysis)

;;; test-git-analysis.el ends here
