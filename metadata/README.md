# Machine-consumed metadata

The audited artifacts that code depends on — claim manifests, signature
pins, declaration rosters, and the proof-step ledger.  `notes/` holds prose
notes; these files moved out of it on 2026-08-18 because checkers, CI
gates, and the paper site read them by path.

Compat symlinks remain at the old `notes/` paths so in-flight lanes and
older instructions keep working; writes through a symlink land here.  New
references should use `metadata/` directly.

| File | Written by | Read by |
| --- | --- | --- |
| `NON_MF_NUMBERED_CLAIMS.json` | `scripts/regenerate_non_mf_claim_manifest.py` + hand edits | claim-manifest checker, prover CI, paper site |
| `NON_MF_PROOF_LEDGER.md` | hand-audited (re-pin via `check_non_mf_proof_ledger.py --repin-header`) | ledger checker, prose-decl checker, paper site |
| `CLAIM_DECLS.txt`, `NON_MF_CLAIM_DECLS.txt` | hand-maintained rosters | `scripts/Signatures.lean`, `check.py`, claim map |
| `CLAIM_SIGNATURES.md`, `NON_MF_CLAIM_SIGNATURES.md` | `scripts/Signatures.lean` (generated) | signature gates in prover CI |
| `AUDIT_SURFACE.md` | `scripts/StatementClosure.lean` (generated) | audit-surface gate in prover CI |
| `CLAIM_MAP.md` | `scripts/claim_map.py` / hand | claim-map gates |
| `NON_MF_UNCONDITIONAL_BASELINE.txt`, `NON_MF_CONDITIONAL_INVENTORY.md` | hand | unconditionality gate |
| `RELEASE_MANIFEST.json` (generated on demand) | `scripts/release_manifest.py --write` | release tooling |
