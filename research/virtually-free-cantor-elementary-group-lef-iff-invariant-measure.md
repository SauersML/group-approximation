---
rg: 2
id: virtually-free-cantor-elementary-group-lef-iff-invariant-measure
kind: claim
title: UN flagship over virtually free acting groups — EL_N/Z of a minimal topologically free virtually free Cantor system is LEF in every rank iff an invariant measure exists
distinct_from:
  free-group-cantor-elementary-group-lef-iff-invariant-measure: that is the flagship for free acting groups; this is the same dichotomy for every virtually free acting group, through finite-index induction of residual finiteness.
  virtually-free-crossed-product-matricial-iff-invariant-measure: that is the ring-level equivalence; this is the group-level dichotomy with simplicity, (T), and the no-MF-quotient end.
---

**ESTABLISHED** by route `virtually-free-cantor-el-lef-iff-invariant-measure-proof`.
- Every input passed independent review: 171f0f7525, f15928d5c9, 10083fd646, 97bf4bc468.
- The assembly is unreviewed.
- **Scope:** finite coefficient field `F_q`; finitely generated crossed product; minimal topologically free action
  of a virtually free group; LEF for all `N >= 3` iff an invariant probability measure exists; otherwise every MF
  quotient is trivial for `N >= 2n`. The band `3 <= N < 2n` is open.

**Setting.** `Γ` virtually free, acting minimally and topologically freely on the Cantor set `X`, with
`R = LC(X,F_q) ⋊ Γ` finitely generated (so `Γ` is finitely generated). For `N >= 3` put
`S_N = EL_N(R)/Z(EL_N(R))`.

**Claim.** Every `S_N` is an infinite, finitely generated, simple Kazhdan group, and:
1. if `X` carries an invariant probability measure, `S_N` is LEF for every `N >= 3`;
2. if not, for some `n >= 1` every homomorphism from `S_N` to an MF group is trivial for all `N >= 2n`, so those `S_N`
   are neither MF nor LEF.

Hence `S_N` is LEF for every `N >= 3` iff `X` carries an invariant probability measure. Examples of acting groups:
`SL_2(Z)`, `PSL_2(Z)`, free products of finite groups. Root: `kazhdan-elementary-approximation-type-mirrors-ring-type`.

**Open band.** In case 2, the ranks `3 <= N < 2n` are not covered
(`el-n-mf-quotient-below-twice-paradoxical-level-exists`).

## Notes

**Assembly.** The complete derivation is in the route. Summary:
- Simplicity, (T) and finite generation are exactly as in `free-group-cantor-elementary-group-lef-iff-invariant-measure`
  (`steinberg-elementary-groups-are-simple-mod-centre`, `elementary-groups-over-fg-rings-have-property-t`).
- Case 1: `virtually-free-crossed-product-matricial-iff-invariant-measure` (i)⇒(iii) replaces the free-group
  equivalence; the scalar-quotient embedding then makes `S_N` LEF.
- Case 2: `no-invariant-measure-steinberg-elementary-no-mf-quotient`, unchanged (it holds for every ample groupoid).

**Beyond virtually free groups.** Case 1 needs an invariant measure to give matricial models. For groups containing
`Z^2` the topological route fails (`z2-containing-groups-have-non-rf-measure-actions`), and the ring may still have
quantum models (`matricial-z2-sft-crossed-products-give-quantum-tilings`). Individual actions can still be RF
(`rf-toeplitz-subshifts-over-residually-finite-groups`). The conjectured exact class is recorded in
`measure-rf-class-is-exactly-virtually-free-groups`.
