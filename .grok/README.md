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

**This is not optional, and skipping it fails silently.** Project hooks under
`.grok/hooks/` only run once the folder is trusted; until then Grok skips them
without any message, and the PR-only guard below is simply not enforced. Trust is
recorded once in `~/.grok/trusted_folders.toml` (`--trust`, or `/hooks-trust` from
inside a session) and covers repo-local MCP, LSP, and hooks together.

Confirm enforcement is live rather than assuming it: a trusted session prints
`PR-only guard armed ...` at startup from the `SessionStart` hook, and
`grok inspect` lists the project hook under `Hooks`. If neither appears, only the
weaker layers are active -- the deny rules in `config.toml` and the prose rule in
`rules/01-pr-only.md` -- and Grok can still edit and commit on `main`.

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
