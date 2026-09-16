---
rg: 2
id: fournier-facio-simple-factor-via-thompson-f
kind: route
title: Choose the Hyde--Lodha group as the simple factor; it contains Thompson's F, so a non-hyperlinear F makes it non-hyperlinear
target: fournier-facio-simple-factor-not-hyperlinear
requires:
  - hyde-lodha-fp-simple-groups-contain-thompson-f
  - thompson-f-is-not-hyperlinear
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

Artifact Section 6.

**Instantiation.** The target's `S` is the simple input recorded in
`fournier-facio-torsion-free-skeleton`, "Burger--Mozes or Hyde--Lodha". This route fixes
`S = Q_n` for some `n ≥ 2`, for example `Q_2`. The choice is admissible:

- **The construction allows it.** Section 2 of Fournier--Facio, arXiv:2608.02025v2, read from
  the PDF, asks only for "A finitely presented simple torsion-free group S, e.g. a Burger–Mozes
  [BM97] or Hyde–Lodha group [HL25]". The only later use of `S` is that the universal
  torsion-free group contains `P_1 × P_2 × S`.
- **`Q_n` qualifies.** By Hyde--Lodha, arXiv:2302.04805, Theorem 1.3, `Q_n` is finitely presented
  and simple. It is infinite, since it contains `F`. It is torsion-free: if an increasing
  homeomorphism `g` of `R` has `g(x) > x`, then `g^k(x) > x` for every `k ≥ 1`.
- **Consumers do not depend on the choice.** The routes that require the target are
  `fournier-facio-nonhyperlinear-via-simple-factor` and
  `fournier-facio-gamma-not-hyperlinear-via-simple-factor`. They use only that `π|_S` is
  injective, the wreath heredity (W8) of `fournier-facio-nontrivial-quotients-contain-simple-wreath`,
  and heredity of hyperlinearity to subgroups. A grep of those routes and the nodes they cite
  finds no Burger--Mozes structure.

**Proof.** Suppose `F` is not hyperlinear. By `hyde-lodha-fp-simple-groups-contain-thompson-f`,
`F ≤ Q_n`. A subgroup of a hyperlinear group is hyperlinear: restrict the embedding into the
tracial matrix ultraproduct. So `S = Q_n` is not hyperlinear. ∎

**Scope.** This proves the target for a Hyde--Lodha choice of `S` only. For a Burger--Mozes
choice, `tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce` instead shows that the target
would produce a non-Connes-embeddable crossed product of an essentially free action of
`F_2 × F_2`. `F` does not embed in a Burger--Mozes lattice: such a lattice acts properly and
cocompactly on a CAT(0) square complex, so its solvable subgroups are virtually abelian, while
`F ⊇ Z ≀ Z`. This is standard and was not re-read here.

Equivalently, for `S = Q_n`, any proof that the simple factor is hyperlinear proves
`thompson-f-is-hyperlinear`. No reverse implication is known: a hyperlinear `F` would not make
`Q_n` hyperlinear.
