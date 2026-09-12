---
rg: 2
id: separated-finite-normal-subgroup-surjunctivity-proof
kind: route
title: Carry surjunctivity across a finite-index subgroup that meets the finite normal subgroup trivially
target: separated-finite-normal-subgroups-preserve-surjunctivity
requires:
  - surjunctivity-is-a-commensurability-invariant
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Section 4 of the artifact.

1. `E_0 ∩ N = 1` makes the quotient map an isomorphism from `E_0` onto `E_0N/N`, a subgroup of index at
   most `[E:E_0]` in `E/N`.
2. If `E/N` is surjunctive: `E_0` is surjunctive by heredity, and `E` by commensurability invariance.
3. If `E` is surjunctive: `E_0` is surjunctive, and `E/N` by commensurability invariance.
4. For the equivalence of hypotheses: a finite quotient injective on `N` has kernel of finite index
   meeting `N` trivially, and the normal core of `E_0` is such a kernel.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 6.3 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
