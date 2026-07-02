# Overview

The lgtm.el package provides a Magit-inspired UI for reviewing code. It provides out-of-the
box support for Github PRs.  It is designed to be adapted to different hosting platforms.  The name,
Looks Good to Me, is ironic because that is the only review that the package will not allow users to
leave. (That is a joke, but you shouldn't do it).

Some of the design principles of lgtm.el are:
- Support reviews of *changesets* (i.e., coordinated commits that span multiple packages)
- Leave repository management to other tools; the caller must ensure that repositories exist on disk
- Bring development tools into the review process

This package expects the user or hosting platform adapter arranges for changesets to be checked out
for review; it does not provide any mechanisms or infrastructure to fetch changesets from remote
servers. This gives users more flexibility to manage their changesets than would be possible in the
core package. This package focuses on providing a UI that can support review workflows.

While it is inherently pleasant to review code in emacs, the real benefit to lgtm.el's approach to
code review is that the changeset exists on disk as normal files.  As normal files, all of your
normal development workflows (e.g., LSPs) are available to help understand the impact of code
changes.

![lgtm-file-diff-overview](https://github.com/user-attachments/assets/27c9ad3a-1980-4ea6-af95-5e10dc351a62)

## Example Workflow

After importing the package with something like:

```
(require 'lgtm)
(require 'lgtm-github)
```

1. Start a review by calling `lgtm-github-review-pr` with a PR URL
2. Examine the overview of the latest commit by expanding diffs for each modified file
3. Mark modified files as reviewed or not
4. Select modified files for side-by-side review in `ediff`; this view supports attaching comments to source locations
5. Send comments to the server
6. Approve changes

Note that marking files as reviewed is a convenience for the reviewer; it has no semantic meaning
for the review. Reviews can be approved without examining every file.

## Dependencies

lgtm.el attempts to keep its dependency list small:

- magit-section
- uuidgen
- ghub (for the Github adapter)
- (Optional) the native emacs sqlite bindings

# Features

- See an overview of the changes made by a changeset with a Magit-inspired UI
- Review changes that span multiple repositories (if supported by your code review service) using `ediff`
- Read comment on changesets
- Leave comments on changesets
- Track which modified files have been reviewed
- Persist review state locally until it is submitted to the server
- Changesets are files on disk, so your normal development tools (e.g., LSPs) just work

## Github Adapter Notes

The Github adapter uses the [ghub](https://github.com/magit/ghub) package to interact with Github.
The easiest way to set up auth is to create a personal access token.  With that, you can add an
entry like the following to `~/.authinfo.gpg`:

```
machine api.github.com login $USERNAME^lgtm password $TOKEN
```

There are currently some limitations in the Github adapter:

- Due to limitations in the Github REST API, it can only leave line-level comments on lines that appear in a PR diff

# Installation

To install using straight.el:

```
(use-package lgtm
  :straight (:host github :repo "travitch/lgtm.el")
  :commands (lgtm-github-review-pr)
  :init
  ;; Optional configuration
  (setopt lgtm-comment-major-mode #'markdown-mode))
```

# Configuration

No configuration should be required to use lgtm unless you need to build an adapter for a new host.

The following configuration options can customized:

- `lgtm-comment-major-mode` specifies the mode used to render comments in the UI as well as the major mode used to edit comments
- `lgtm-comment-mode-hook` is a hook called after `lgtm-comment-major-mode` is enabled in the comment editor
- `lgtm-timestamp-format` is the format string passed to `format-time-string` to format timestamps
- `lgtm-comment-editor-banner` is the format that should be used to render a banner in the comment editor; it can be set to `nil` to suppress the banner

The default comment major mode is the built-in `text-mode`.  You are likely to want to change it to
`markdown-mode`.  The only reason that Markdown is not the default is to minimize dependencies.

# Concepts

lgtm.el has the following UI elements:

- The overview UI showing changeset metadata, changed files, and diffs
- The `ediff` UI for reviewing the changes within a file (including line-level comments)
- The comment editing interface, which is just a standard buffer

## File Revisions

When reviewing files, lgtm.el refers to the original version of the file before the change as the
*base* revision and the version of the file after the change is applied as the *current* revision.

## Reviewing Changes

Pressing `<TAB>` on a modified file in the overview UI shows a diff of the changes applied to the
file by the changeset.  This can be sufficient for small changes.  For more extensive changes,
pressing `<RET>` on a modified file brings up the changed file in `ediff`.  The `ediff` UI has
keybindings to navigate change hunks and view line-level comments.

## Comments

Comments are threaded and can be either 1) top-level comments visible in the overview UI or 2)
line-level comments shown in the `ediff` review UI.  Comments can be created in either the *base*
revision or the *current* revision.

# Keybindings

The keybindings can be changed freely.  The defaults for each part of the UI are as follows.

## Overview UI

- `RET` on a modified file launches the `ediff` file review UI for that file (`lgtm-review-selected-modified-file`)
- `TAB` collapses or expands regions (as in `magit-section`); shows diffs or top-level comments when the point is on one
- `R` marks the selected file as reviewed (`lgtm-mark-selected-modified-file-reviewed`)
- `U` marks the selected file as unreviewed (`lgtm-mark-selected-modified-file-unreviewed`)
- `S` publishes draft comments (`lgtm-submit-comments`)
- `A` approves the changeset and publishes any draft comments (`lgtm-approve`)
- `q` closes lgtm and cleans up any associated buffers (`lgtm-shutdown`)

The overview UI also inherits all of the default keybindings from `magit-section`.

## Ediff File Review UI

- `n` highlights the next changed hunk in the diff (`lgtm-next-hunk`)
- `p` highlights the previous changed hunk in the diff (`lgtm-previous-hunk`)
- `M-n` selects the next thread (`lgtm-select-next-thread`)
- `M-p` selects the previous thread (`lgtm-select-previous-thread`)
- `C-M-n` selects the next comment in the currently-selected thread
- `C-M-p` selects the previous comment in the currently-selected thread
- `R` opens the comment editor to draft a reply to the selected comment (`lgtm-reply-to-selected-comment`)
- `C` opens the comment editor to draft a comment that covers the lines in the file selected by the region (`lgtm-conversation-dwim`)
- `0` resets the selected comment (`lgtm-clear-selected-comment`)
- `q` closes the `ediff` file review UI and cleans up the associated buffers (`lgtm-close-review-file`)

The following keybindings only work if the focus is in either the base or current revision buffers:

- `C-c C-c` focuses the `ediff` control pane (`lgtm-jump-to-ediff-control-pane`)

The following keybindings only work if the `ediff` control pane is focused:

- `v` scrolls the base and current revision buffers down in lockstep
- `V` scrolls the base and current revision buffers up in lockstep

## Comment Editing UI

The comment editor enables the `lgtm-comment-major-mode` (e.g., `markdown-mode`), including all of
the relevant keybindings.  Beyond that, lgtm.el introduces two key bindings:

- `C-c C-c` to create a new draft comment from the contents of the comment buffer (`lgtm-complete-comment`)
- `C-c C-k` to cancel the creation of the comment and discard the contents of the comment buffer (`lgtm-quit-comment`)

# Similar Packages

There are a few other code review UIs for emacs.

## git-review

This package builds on ideas and some code from `git-review`
(https://git.sr.ht/~niklaseklund/git-review). This package uses the `ediff` UI, but significantly
changes the data model and discards all of the features for managing worktrees.

## code-review

The `code-review` package (https://github.com/wandersoncferreira/code-review) is a generic code
review package that provides a Magit-like interface for code review. It supports Github, Gitlab, and
Bitbucket. It provides deeper integrations with forges than `lgtm`; however, that makes it more
difficult to customize. Adding support for code reviews that span multiple coordinated repositories
would have been difficult.

## emacs-review-pr

The `emacs-review-pr` package (https://github.com/blahgeek/emacs-pr-review) is a similar system
specialized to Github pull requests.  It supports more Github features than `lgtm` (e.g., showing
the status of automated checks).  It provides a diff-oriented view of changes in the same style as
the Github web UI, while `lgtm` is attempting to provide a more interactive review experience and
make development tools available during the review process.
