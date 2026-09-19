# Grok PR-only workflow

These rules apply to Grok Build only.

- Treat `main` and `master` as protected integration branches. Never edit project files, commit, merge, or push while checked out on either branch.
- Before changing code, synchronize the integration branch, then create a fresh branch named `grok/<short-task>`.
- Make one focused change per branch. Keep unrelated edits out of the branch.
- Run the relevant checks before publishing. For repository-wide Lean changes, use `lake build`; for narrower work, run the smallest meaningful Lean/build/test command first and include any remaining failures in the PR description.
- Commit and push only the `grok/*` branch.
- Deliver every change by opening a pull request against `main`, for example with `gh pr create --base main --head <branch>`.
- Never merge a PR, enable auto-merge, bypass review, or push directly to `main`/`master`. After opening or updating the PR, stop and report the PR URL and validation status. A human merges.
- Leanstral is a separate tool/workflow. Do not configure, invoke, proxy through, or modify Leanstral as part of Grok setup or Grok tasks unless the user explicitly asks for a Leanstral change.
