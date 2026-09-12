---
rg: 2
id: strict-memory-residual-kernel-proof
kind: route
title: Restrict a strict automaton to its memory group and apply the separated finite normal transfer there
target: strict-automata-memory-keeps-finite-normal-kernel-residual
requires:
  - separated-finite-normal-subgroups-preserve-surjunctivity
  - surjunctivity-passes-to-subgroups
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Section 3 of the artifact.

1. **Coset restriction (Lemma 3.1).** The cells `g` and `gm` with `m in M` share the left coset `gH`. So
   `A^E` is a product over `E/H` of copies of `A^H`, and `tau` acts as `tau_H` on each copy. Injectivity and
   surjectivity are coordinatewise, so `tau_H` is strict.
2. **Separated case excluded.** If `H cap N` injected into a finite quotient of `H`, the separated transfer
   would make `H` surjunctive iff `HN/N` is. `HN/N <= E/N` is surjunctive by heredity, contradicting step 1.
3. **Residual form.** `N` is finite. If `N cap Res_fin(H) = 1`, finitely many finite-index normal
   subgroups of `H` avoid each nontrivial element of `H cap N`, and their intersection `K` has finite index
   with `K cap N = 1`, so `H cap N` injects into `H/K`. Conversely an injection into `H/K` gives
   `Res_fin(H) cap N <= K cap N = 1`.
4. **Nonsofic.** A sofic `H` is surjunctive by Gromov–Weiss, against step 1.

**Verification.** `w3-vf-positive` passed this route (Section 7.3 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
