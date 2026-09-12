---
rg: 2
id: mf-kazhdan-without-finite-quotients-citation
kind: route
title: Import Ozawa--Thom's residually finite quotient theorem for weakly quasidiagonal Kazhdan groups
target: mf-kazhdan-group-without-finite-quotients-is-trivial
requires: []
---

Literature import plus a two-line deduction.  The source is M. Dadarlat,
*Obstructions to matricial stability of discrete groups and almost flat
K-theory*, arXiv:2007.12655v2, the same source and propositions already used
by `exact-kazhdan-radical-kernel-cannot-be-lef-proof`.

Read 2026-09-11 (ar5iv HTML):

- Definition 3.1: "A group `G` is MF if it is isomorphic to a subgroup of the
  unitary group of an MF-algebra."  An MF algebra embeds in the matrix corona,
  so this is the repository's operator-MF notion.
- Definition 3.10: `G` is weakly quasidiagonal "if there is a ucp asymptotic
  homomorphism `{φ_n : C*(G) → M_{k_n}}_n` which separates the points of `G`",
  and Section 3 records that MF implies weak quasidiagonality.
- Proposition 3.19 (Ozawa--Thom): "If an infinite property (T) group `G` is
  weakly quasidiagonal, then `G` has an infinite residually finite quotient."

Deduction.  Let `G` be MF, Kazhdan, and without nontrivial finite quotients.
If `G` were infinite, Proposition 3.19 gives an infinite residually finite
quotient `q : G -> Q`.  Choose `x != 1` in `Q` and a finite quotient
`f : Q -> F` with `f(x) != 1`; then `f o q` is a nontrivial finite quotient of
`G`, a contradiction.  So `G` is finite, and a nontrivial finite group is its
own nontrivial finite quotient.  Hence `G = 1`.

Trust surface: the MF-to-weak-quasidiagonality passage and Proposition 3.19
were read through the HTML rendering, and their proofs were not re-derived.
