---
rg: 2
id: some-quotient-of-braided-v-is-not-finitely-presented
kind: claim
title: Some quotient of the braided Thompson group bV is not finitely presented
distinct_from:
  every-quotient-of-braided-v-is-finitely-presented: that claim is the opposite answer to the same question; exactly one of the two holds
---

There is a normal subgroup `N` of `bV = V_br` that is not the normal closure of
finitely many elements. Equivalently, `bV/N` is not finitely presented. By
Corollary 2.8 of arXiv:1403.8132, any such `N` lies in the pure braided kernel
`P_br`.

## Attempts

- 2026-09-13 (z2-10-bv-hopfian): a counting argument would suffice. `bV` has only
  countably many normally finitely generated subgroups, so uncountably many normal
  subgroups would finish.
  - Where it dies: each graded piece `gamma_c/gamma_{c+1}` of `P_br` has only
    countably many `V`-invariant subgroups, since it is a noetherian `FS^op`-module
    over a countable ring. An uncountable family would have to mix infinitely many
    depths.
- Candidate: `[P_br, P_br]`. If `bV/[P_br, P_br]` is not finitely presented, this
  claim holds. That quotient is an extension of `V` by the module `C_c(Y, Z)` of
  `braided-thompson-group-bv-is-perfect`.
