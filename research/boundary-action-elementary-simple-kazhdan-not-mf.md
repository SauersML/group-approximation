---
rg: 2
id: boundary-action-elementary-simple-kazhdan-not-mf
kind: claim
title: EL_3 of LC(∂F_2, F_2) ⋊ F_2 mod centre is an infinite fg simple Kazhdan group with no nontrivial MF quotient - the paradoxical mirror of the Pestov 9.1 group
distinct_from:
  simple-kazhdan-lef-group-from-minimal-subshift: that is S = EL_3(LC(X,F_q) ⋊ Z)/Z for a minimal Z-subshift, which carries an invariant measure and is LEF; this is the same construction for the boundary action of F_d, which has no invariant measure and has no nontrivial MF quotient.
  paradoxical-steinberg-families-kazhdan-no-mf-quotient: that gives the elementary groups themselves; this adds simplicity modulo the centre for the boundary-action family.
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

Let `d >= 2`, `k` a countable field, `F_d` acting on its boundary `∂F_d` (infinite reduced words), and
`R = LC(∂F_d, k) ⋊ F_d`, the algebraic crossed product. For `N >= 3` put
`S_∂ = EL_N(R) / Z(EL_N(R))`. Then `S_∂` is:

1. infinite and finitely generated;
2. simple;
3. Kazhdan;
4. such that every homomorphism from `S_∂` to an MF group is trivial. In particular `S_∂` is not MF.

**The mirror.** The Pestov 9.1 group is `S = EL_3(LC(X, F_2) ⋊ Z)/Z` with `X` a minimal subshift. Both
rings are Steinberg algebras of minimal effective transformation groupoids on the Cantor set, and both
groups are infinite, finitely generated, simple and Kazhdan by the same two criteria:
- ring simplicity from minimality plus effectiveness;
- group simplicity from local annihilation;
- plus Ershov–Jaikin-Zapirain.

The single difference is the dynamics:
- The Z-subshift carries an invariant measure and admits return towers, so `S` is LEF.
- The boundary action is paradoxical, `2[∂F_d] <= [∂F_d]` in the type semigroup, so `S_∂` has no
  nontrivial MF quotient.

Unreviewed. The simplicity inputs are un-simplicity's established but unreviewed nodes.
