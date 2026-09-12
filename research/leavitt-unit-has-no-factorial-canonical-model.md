---
rg: 2
id: leavitt-unit-has-no-factorial-canonical-model
kind: claim
title: No canonical matrix model of the binary Leavitt unit group has factorial global commutant
distinct_from:
  factorial-leavitt-models-have-external-corner-commutants: that proves the native corner commutant of any factorial canonical model is external; this asserts that no factorial canonical model exists at all.
  leavitt-steinberg-hs-stable: that is normalized-HS stability of the group; this is nonexistence of one class of models, which implies stability only together with the open existence input for that class.
  binary-leavitt-unit-group-hyperlinear: that asks whether any faithful model exists; this excludes only models whose global commutant is a factor.
---

**OPEN.** Let `H = L_(F_2)(1,2)^x`. There is no homomorphism
`pi : H -> U(prod_omega M_(d_n))` with regular trace `tau o pi = delta_1`
whose global commutant `pi(H)' cap prod_omega M_(d_n)` is a factor.

Scope:
* Given `leavitt-unit-hyperlinear-gives-factorial-canonical-model`, this
  claim is equivalent to nonhyperlinearity of `H`, and so to
  `leavitt-steinberg-hs-stable` (`leavitt-unit-hs-stable-iff-nonhyperlinear`).
* By `factorial-leavitt-models-have-external-corner-commutants`, a factorial
  canonical model always has an external native corner commutant. So this
  claim is equivalent to: in every factorial canonical model the native corner
  commutant is an ultraproduct of finite-dimensional coordinate algebras, as
  in Alekseev--Thom Open Problem 6.2(a). That instance of 6.2(a) is the attack
  surface. No selection of a scalar-commutant model is needed.

## Attempts

- **Corner internality.** Prove 6.2(a) for the native `EL_3` corner in
  factorial models.
  - What must be excluded is exactly Jones-index growth of a type II_1
    commutant under the compressor: `Ad pi(u)` carries `D = pi(L)' cap M`
    onto `pi(uLu^(-1))' cap M`, which contains `D`, the way `R` sits inside
    `R (x) M_2`, with no central height. `trace-blindness-sharpness` already
    realizes such growth, `uNu* ⊊ N`, in a Bernoulli crossed product, which is
    why `invariant-size-argument` is dead. So only coordinate structure can
    help.
  - The finite-dimensional central-height lemma needs coordinate algebras to
    see the drift. Normalized HS supplies no dimension-conservation tool for a
    non-internal commutant, and every known rounding class (cb factorizations,
    Schur channels, twirls, bounded Kraus minorants, near-fixed masas) excludes
    native heat maps. Open.
- **Central decomposition by property (T).**
  - If `z` is central in the global commutant, the compressions of `pi` to `z`
    and `1-z` have no nonzero intertwiners. A Kazhdan constant then separates
    them by a fixed distance on a generating set.
  - Separation of disjoint central summands does not force an atom, so it
    cannot rule out diffuse centres. Nor does it produce a factorial summand.
    Dead as a nonexistence proof.
- **Commutant structure.** Popa, arXiv:1308.3982 (Section 1): the commutant
  of a separable subalgebra is atomic plus a diffuse part with no separable
  direct summand. A factorial commutant is therefore finite-dimensional or a
  diffuse factor without separable summands. Neither case is excluded by that
  structure theorem.
