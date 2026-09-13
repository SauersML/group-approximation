---
rg: 2
id: sl4z-corona-representations-have-block-sl2-norm-four
kind: claim
title: Every corona representation of SL_4(Z) gives the block SL_2(Z) Laplacian norm four
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that is the published theorem for genuine finite-dimensional representations; this asks the same norm conclusion for asymptotic homomorphisms, that is for every unital map into a matrix corona.
  sl4z-matricially-stable: that asks every asymptotic homomorphism to be near a genuine representation; this asks only that the block SL_2(Z) Laplacian keep norm four, which stability implies.
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md
---

OPEN.  Let `z = S + S^(-1) + T + T^(-1)` for the upper-left block `SL_2(Z)` of
`SL_4(Z)`.  Every unital *-homomorphism
`pi : C*(SL_4(Z)) -> prod_n M_(k_n) / sum_n M_(k_n)` satisfies `||pi(z)|| = 4`.

**An equivalent finite form** (artifact, Section 4, Theorem 2).  For every `eta > 0` there are a finite
`F subset SL_4(Z)` and `delta > 0` such that every map `phi : SL_4(Z) -> U(k)` with
`||phi(gh) - phi(g) phi(h)|| < delta` for `g, h in F` has
`||phi(S) + phi(S)^* + phi(T) + phi(T)^*|| >= 4 - eta`.  This is a robust version of
Magee--de la Salle Theorem 1.1, which is the case of genuine representations.

**Consequences.**
- It implies `sl4z-reduced-cstar-is-not-mf`, and non-MF of `C*_r(Gamma)` for every
  `Gamma` containing `SL_4(Z)` (route `sl4z-reduced-not-mf-from-corona-block-sl2-norm-four`).
- It is implied by `sl4z-matricially-stable` (route
  `sl4z-corona-block-sl2-norm-four-from-matricial-stability`), so it is a weaker crux
  for the same root.

## Attempts

* **The congruence side.**  Handled, and landing next with part 2 of the artifact.
  Suppose the joint spectrum of the column unipotent `Z^3` is not all of `T^3`.  Then the
  representation factors through some `SL_4(Z/NZ)` and has norm four.  What remains is
  the full-spectrum case, which contains every MF embedding.
* **MdlS Step 3 at non-torsion characters.**  Dead
  (`mdls-averaging-at-non-torsion-character-gives-spectral-gap`).  Averaging an
  eigenvector of a non-torsion character over the block `SL_2(Z)` produces a
  representation weakly contained in `lambda_SL2(Z)`, whose Laplacian norm is `< 4`.
* **Torsion points inside a full spectrum.**  Not worked out.
  - The countable saturation of the corona gives fibre elements at a level-`p^r` spectral
    point that commute with the stabilizer of the character.
  - Step 3's finite average then needs invariance under a principal congruence subgroup
    of the block `SL_2(Z)`, and a representation that factors through no `SL_4(Z/p^r)`
    does not supply it.
  - No substitute found.
