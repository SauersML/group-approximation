# Grok Build

Grok Build is configured here as a separate coding agent alongside the repository's existing Leanstral workflow. Grok and Leanstral are not connected, proxied, or orchestrated through each other.

## Install

```bash
curl -fsSL https://x.ai/cli/install.sh | bash
grok --version
```

## Arming the guard

Grok 0.2.93 does **not** load hooks from `<project>/.grok/hooks/`. This is measured,
not inferred: with only a project hook present, Grok edited a file on `main` without
the guard ever running, and `grok inspect` listed no project hook. Folder trust is not
the cause -- `projectTrusted` was already true. Global hooks under `~/.grok/hooks/` do
load, so that is where the guard has to be reachable from:

```bash
./.grok/install-global-hook.sh
```

That installs `hooks/global-loader.json` as `~/.grok/hooks/pr-only.json`. The loader is
repository-agnostic: it runs `$GROK_WORKSPACE_ROOT/.grok/hooks/pr-only-guard.py` when the
current workspace ships one and exits 0 otherwise, so it enforces this repository's policy
here and imposes nothing on any other repository on the machine. Both halves are covered by
`.grok/hooks/test_pr_only_guard.py`, which CI runs on every change under `.grok/`.

Confirm it is live rather than assuming: `grok inspect` should list a `command ... user`
entry under `Hooks`, and a session started in this repository on `main` should be unable to
edit a file. `.grok/hooks/pr-only.json` is kept as the project-level declaration for when
xAI wires project hooks up; it is inert today and harmless.

Inspect the loaded project configuration with:

```bash
grok inspect
```

## Grok repository policy

Grok is PR-only:

1. Start from an up-to-date `main`.
2. Create a `grok/<task>` branch before editing.
3. Make and validate the change on that branch.
4. Push only that branch.
5. Open a PR targeting `main`.
6. Stop after the PR is open; a human reviews and merges it.

Leanstral keeps its existing independent workflow under `.github/workflows/leanstral-research.yml` and `scripts/leanstral_novelty.py`.

Grok's policy is defined in `.grok/rules/01-pr-only.md`, backed by native deny rules in `.grok/config.toml`, and enforced by `.grok/hooks/pr-only-guard.py` when the project is trusted.
