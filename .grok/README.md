# Grok Build

Grok Build is configured here as a separate coding agent alongside the repository's existing Leanstral workflow. Grok and Leanstral are not connected, proxied, or orchestrated through each other.

## Install

```bash
curl -fsSL https://x.ai/cli/install.sh | bash
grok --version
```

Start Grok from the repository root with project hooks trusted:

```bash
grok --trust
```

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
