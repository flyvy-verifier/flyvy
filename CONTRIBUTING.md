# Contributing to temporal-verifier

We welcome contributions from the community and first want to thank you for taking the time to contribute!

Please familiarize yourself with the [Code of Conduct](https://github.com/vmware-research/temporal-verifier/blob/main/CODE_OF_CONDUCT.md) before contributing.

Before you start working with temporal-verifier, please read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on as an open-source patch.

## Submitting a pull request

* Push your code to a branch on the repository.
* Create a pull request to merge that branch into `main`.
* In response to feedback, you can push small commits to the same branch to
  update the PR; these commits are often easier to review than if you
  force-push. If a comment is clearly addressed, feel free to mark it as
  resolved, otherwise leave them to the reviewer as a checklist.
* If there are merge conflicts, feel free to rebase on top of main, and to
  squash commits into logical groupings. You can use `git rebase -i origin/main`
  to do this.

Try to avoid long-lived pull requests, as these lead to more conflicts and get
harder to review. We aim to merge or close pull requests quickly (say, within a
month).

## Must-haves for every commit pushed to this repository

* Do not push to `main` without asking. Instead, use a branch and create a pull request.
* Every commit must be signed (see above). Use `git -s` or otherwise add
  `Signed-off-by: Your Name <your@email.com>` to the last line of each Git
  commit message. You can get git to add this line automatically when you start
  editing a commit message by copying `tools/prepare-commit-msg` to `.git/hooks/`.
* Every code file in the repository must start with a two-line copyright notice:
  ```rust
  // Copyright 2022-2023 VMware, Inc.
  // SPDX-License-Identifier: BSD-2-Clause
  ```
  or
  ```python
  # Copyright 2022-2023 VMware, Inc.
  # SPDX-License-Identifier: BSD-2-Clause
  ```
* Before creating a commit, make sure the following tests pass (these are run by CI on GitHub, so the commit will get a :x: if they don't). You can run `./tools/ci-check.sh` to run all of these automatically.
  * `cargo test`
  * Use `cargo fmt` to format the code. You can use the "format on save" setting in VS Code to have this done automatically.
  * Run `cargo clippy --tests` and make sure there are no warnings. In VS Code you can run this check automatically on save by opening user preferences and adding `"rust-analyzer.checkOnSave.command": "clippy"`.
* Commit messages should generally follow this [style guide](http://chris.beams.io/posts/git-commit/). In short:
  * Use a short summary title, and add a longer body if needed.
  * Use imperative style ("Fix bug" and not "Fixed bug", "Fixes bug", or "Bugfix"). The title should read like "if you apply it, this commit will ..." or "after applying this commit, the code will...".
  * Keep the title short, GitHub truncates at 72 charachters.
  * The blank line separating the title from the body is critical (unless you omit the body entirely).
  * The blank line before the `Signed-off-by` is also critical.

   Here's an example:
  ```
  Use short title with capital letter and without period

  A longer paragraph can explain more (but it's not always needed).
  * Maybe a bullet point
  * Or two

  Another paragraph can be used if needed.
  * But multiple small commits are preferred over a large commits

  Signed-off-by: Your Name <your@email.com>
  ```

## Ways to contribute

We welcome many different types of contributions and not all of them need a Pull request. Contributions may include:

* New features and proposals
* Documentation
* Bug fixes
* Issue Triage
* Answering questions and giving feedback
* Helping to onboard new contributors
* Other related activities

## Getting started

* Please see the [README](https://github.com/vmware-research/temporal-verifier/blob/main/README.md) for instructions on how to build this project.
* If you're contributing code, please make sure that the project builds and passes all tests with your changes.

## Contribution Flow

This is a rough outline of what a contributor's workflow looks like:

* Make a fork of the repository within your GitHub account
* Create a topic branch in your fork from where you want to base your work
* Make commits of logical units
* Make sure your commit messages are with the proper format, quality and descriptiveness (see below)
* Push your changes to the topic branch in your fork
* Create a pull request containing that commit

We follow the GitHub workflow and you can find more details on the [GitHub flow documentation](https://docs.github.com/en/get-started/quickstart/github-flow).

### Pull Request Checklist

Before submitting your pull request, we advise you to use the following:

1. Check if your code changes will pass both code linting and format checks (`cargo fmt --check`) and unit and regression tests (`cargo test`).
2. Ensure your commit messages are descriptive. We follow the conventions on [How to Write a Git Commit Message](http://chris.beams.io/posts/git-commit/). Be sure to include any related GitHub issue references in the commit message. See [GFM syntax](https://guides.github.com/features/mastering-markdown/#GitHub-flavored-markdown) for referencing issues and commits.
3. Check the commits and commits messages and ensure they are free from typos.
4. Any new modules or new public functions should have a rustdoc comment.
5. Strive for 100% statement coverage via tests (unit tests or snapshot tests are both good). For example, if you are writing a function that traverses the AST, make sure there is a test where every possible kind of AST node is passed to your function. Don't forget to test error paths, especially for user-facing code. Users make great fuzzers, so you shouldn't assume anything about user-provided input that you haven't checked yourself.

## Reporting Bugs and Creating Issues

For specifics on what to include in your report, please follow the guidelines in the issue and pull request templates when available.

## Ask for Help

The best way to reach us with a question when contributing is to ask on the original GitHub issue, or open a new issue.
