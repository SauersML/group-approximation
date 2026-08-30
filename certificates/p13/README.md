# P13 certificate

This directory contains the reproducibility inputs for the exact P13 Hodge
certificate checked by Lean under `GroupApproximation/Sofic/`.

- `sl3-sos-radius0-certificate.npz` stores the exact integer Gram factor.
- `sl3-p13-reductions-complete.json` stores proof-carrying word reductions.
- The Python generators reproduce the checked-in Lean certificate modules.

The binary and JSON files are not trusted proof inputs. Lean rechecks the
emitted equalities from the abstract presentation. To reproduce every
generated module, run from the repository root:

```sh
uv run python scripts/check_p13_generated.py --temporary-root /tmp
```
