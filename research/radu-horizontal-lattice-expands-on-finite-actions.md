---
rg: 2
id: radu-horizontal-lattice-expands-on-finite-actions
kind: claim
title: The horizontal lattice C_chi = <a,b,cac,cbc> has a uniform Cheeger constant on its orbits in every finite action of Radu's arithmetic quotient
distinct_from:
  radu-square-lamp-forces-reflections-in-finite-actions: that is an exact statement about fixed points of C_chi in finite Q-sets, with no expansion; this is the expansion input that makes it robust to small invariance defects
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that is property tau for SL_2(Z) inside SL_2(Z[1/p]); this is the analogous statement for the quaternionic pair under Radu's lattice
---

**OPEN.** There is `h > 0` with the following property. For every action `ρ` of `Q` on a finite set,
every `ρ(C_χ)`-orbit `O`, and every `P ⊂ O`, the edge boundary of `P` in the Schreier graph on
`a, b, cac, cbc` has at least `h·min(|P|, |O \ P|)` edges. This is the "super-strong approximation" input
of the lane's brief, stated for all finite actions.

## Attempts

* **Congruence actions (recalled, not verified).** `C` has finite index in the stabilizer in `Q` of a
  vertex of the second tree, a `{𝔮}`-arithmetic lattice of the totally definite quaternion algebra
  over `Q(√17)`. Its congruence Schreier graphs have a uniform spectral gap, by property τ for
  congruence subgroups of arithmetic groups (Clozel), or for this inner form of `SL_2` via
  Jacquet–Langlands and a Ramanujan-type bound. A `C_χ`-orbit in a congruence `Q`-set is a quotient of
  a congruence quotient of `C_χ`, so it inherits the gap. The sources are not re-read.
* **Arbitrary finite actions.** These reduce to congruence actions if `Q` has the congruence subgroup
  property. `Q` is an `S`-arithmetic lattice of `S`-rank 2 in an anisotropic inner form of type
  `A_1`, and the literature status of that case was not checked here.
* **Model test.**
  - *A model that fails it.* The same statement over all finite actions of `C_χ` itself is false.
    `C_χ ≅ C_2^(*4)` is virtually free, so it has finite quotients with no uniform gap: take large
    cycles in the Schreier graph of a finite-index subgroup onto `Z`.
  - *So the restriction matters.* The claim has content only because the actions are required to
    extend to `Q`.
  - *A real object that satisfies it.* The analogous pair `SL_2(Z) < SL_2(Z[1/p])`, by Selberg's
    bound together with Serre's congruence subgroup property, as used in
    `hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable`.
