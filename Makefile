TEST_DIR=$(shell pwd)/test

.PHONY: test

test:
	eask prepare
	eask test ert $(TEST_DIR)/test-comment-index.el \
		$(TEST_DIR)/test-git-parsing.el \
		$(TEST_DIR)/test-git-analysis.el \
		$(TEST_DIR)/test-github-utils.el
