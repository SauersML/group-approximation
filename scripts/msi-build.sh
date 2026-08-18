#!/usr/bin/env bash
# Compatibility shim.  The real script is scripts/remote-build.sh, which is
# TRACKED; this path stays only so in-flight commands and muscle memory keep
# working.  Site configuration lives in scripts/remote-build.env (gitignored).
#
# Why the split: this file is gitignored because it embedded one person's
# cluster account details, so the build logic every lane depends on could not
# be reviewed, versioned, or obtained from a fresh clone.  On 2026-08-16 its
# orphan scan turned a no-argument invocation into a ~300-target full-corpus
# build that held the fleet lock and queued two other lanes -- a bug in code
# nobody could see.  The logic now lives in a tracked file; only the account
# details stay out.
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/remote-build.sh" "$@"
