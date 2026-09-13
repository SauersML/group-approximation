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
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13-part2.md
---

OPEN.  Let `z = S + S^(-1) + T + T^(-1)` for the upper-left block `SL_2(Z)` of
`SL_4(Z)`.  Every unital *-homomorphism
`pi : C*(SL_4(Z)) -> prod_n M_(k_n) / sum_n M_(k_n)` satisfies `||pi(z)|| = 4`.

**Finite form** (artifact part 1, Section 4, Theorem 2).  An equivalent statement: for
every `eta > 0` there are a finite `F subset SL_4(Z)` and `delta > 0` such that every map
`phi : SL_4(Z) -> U(k)` with `||phi(gh) - phi(g) phi(h)|| < delta` for `g, h in F` has
`||phi(S) + phi(S)^* + phi(T) + phi(T)^*|| >= 4 - eta`.  This is a robust version of
Magee--de la Salle Theorem 1.1, which is the case of genuine representations.

**Consequences.**
- It implies `sl4z-reduced-cstar-is-not-mf`, and non-MF of `C*_r(Gamma)` for every
  `Gamma` containing `SL_4(Z)` (route `sl4z-reduced-not-mf-from-corona-block-sl2-norm-four`).
- It is implied by `sl4z-matricially-stable` (route
  `sl4z-corona-block-sl2-norm-four-from-matricial-stability`), so it is a weaker crux
  for the same root.

## Attempts

* **Congruence side.**  Done: `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`.
  - If the joint spectrum of the column unipotent `Z^3` is not all of `T^3`, the
    representation factors through some `SL_4(Z/NZ)` and has norm four
    (`sln-z-unipotent-spectrum-finite-or-full-torus`).
  - So the claim is equivalent to its full-spectrum case, which contains every MF
    embedding.
* **MdlS Step 3 at non-torsion characters.**  Dead
  (`mdls-averaging-at-non-torsion-character-gives-spectral-gap`).  Averaging an eigenvector
  of a non-torsion character over the block `SL_2(Z)` gives a representation weakly
  contained in `lambda_SL2(Z)`, whose Laplacian norm is `< 4`.
* **Torsion atoms inside a full spectrum.**  Not closed.
  - Countable saturation of the corona gives fibre elements at a level-`p^r` spectral
    point, and they can be made to commute with the stabilizer of the character.
  - Step 3's finite average then needs invariance under a principal congruence subgroup
    of the block `SL_2(Z)`.  A representation that factors through no `SL_4(Z/p^r)` does
    not supply it.
  - No substitute found (artifact part 2, Section 4).
* **Continuous spectral part.**  Open.
  - The firewall does not reach it: `Z^2 x| SL_2(Z)` on `l^2(Z^2)` has Haar spectrum for
    `Z^2` and still an `SL_2(Z)`-fixed vector `delta_0`.
  - Refuting the claim needs an asymptotic homomorphism of `SL_4(Z)` that is not near any
    genuine representation and has block-`SL_2` spectral gap.  That would also refute
    `sl4z-matricially-stable`.
