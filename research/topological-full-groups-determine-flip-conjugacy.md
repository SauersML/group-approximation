---
rg: 2
id: topological-full-groups-determine-flip-conjugacy
kind: claim
title: Two Cantor minimal systems are flip conjugate iff their topological full groups are isomorphic as abstract groups
---

Let `(X,φ)` and `(Y,ψ)` be Cantor minimal systems. The topological full group `[[φ]]` is the group of homeomorphisms
`γ` of `X` with `γ(x) = φ^(n_γ(x))(x)` for a continuous `n_γ: X → Z`. `[[φ]]_0` is the kernel of the index map, and
`D([[φ]])` is the commutator subgroup.

Then `(X,φ)` and `(Y,ψ)` are flip conjugate, meaning a homeomorphism `F: X → Y` has `F∘φ∘F^(-1) ∈ {ψ, ψ^(-1)}`, if and
only if `[[φ]] ≅ [[ψ]]` as abstract groups. The same holds with `[[φ]]_0` in place of `[[φ]]`, and with `D([[φ]])`.

Credit:
- Giordano–Putnam–Skau, *Full groups of Cantor minimal systems*, Israel J. Math. 111 (1999), 285–320, for `[[φ]]` and
  `[[φ]]_0`.
- Bezuglyi–Medynets, *Full groups, flip conjugacy, and orbit equivalence of Cantor minimal systems*, Colloq. Math. 110
  (2008), 409–429, arXiv:math/0611173, Theorem 5.13, which adds `D([[φ]])` and gives a unified proof through spatial
  realization (their Theorem 5.8) and Boyle–Tomiyama, J. Math. Soc. Japan 50 (1998), Corollary 2.7.

Use: `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`.
