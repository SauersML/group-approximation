---
rg: 2
id: hyperbolic-kac-moody-torsion-lf-proof
kind: route
title: Without Z^2 in W the buildings have no flat planes (Caprace–Haglund), hence are Gromov hyperbolic, so a finitely generated torsion group has bounded orbits on both (Haettel–Osajda) and lies in a finite stabilizer of a pair of chambers
target: hyperbolic-kac-moody-lattices-are-torsion-locally-finite
requires:
  - two-dim-cat0-product-groups-are-torsion-locally-finite
  - simple-kazhdan-kac-moody-lattices-exist
---

## Inputs

- **(HO)** Haettel–Osajda, "Locally elliptic actions, torsion groups, and nonpositively curved spaces",
  arXiv:2110.12431v3. Read at source through the arXiv HTML rendering on 2026-09-18; quoted as returned.
  - **Definitions.** An action is *locally elliptic* if "the orbit of each element is bounded", and *elliptic* if "the
    orbit of the whole group is bounded".
  - **Corollary B.** "Let a finitely generated group act on a complex X which is one of the following: … (2) a
    uniformly locally finite Gromov hyperbolic graph; … If the action is locally elliptic then it is elliptic."
- **(CH)** Caprace–Haglund, "On geometric flats in the CAT(0) realization of Coxeter groups and Tits buildings",
  arXiv:math/0607741v1, p. 3, read at source (PDF). Theorem E: "Let (W,S) be a Coxeter system and 𝓑 be a building of
  type (W,S). Every geometric flat of the CAT(0) realization |𝓑|_0 of 𝓑 is contained in an apartment. In particular,
  one has rk(|𝓑|_0) = alg-rk(W)."
- **(FP)** Flat plane theorem, [BH99, III.H.1.5], cited: a proper cocompact CAT(0) space is Gromov hyperbolic iff it
  contains no isometrically embedded Euclidean plane.
- **Kac–Moody background.** Twin buildings, discreteness and finite pair stabilizers: exactly as in
  `two-dim-cat0-product-groups-torsion-lf-proof`, Item 2.

## Proof

Let `E ≤ Λ` be finitely generated torsion.

1. **The buildings are hyperbolic.**
   - `W` contains no `Z^2`, so `alg-rk(W) <= 1`. By (CH) Theorem E the CAT(0) realization `X_± = |Δ_±|_0` contains no
     2-flat.
   - `X_±` is proper: it is locally finite, since `q` is finite, and has finitely many shapes.
   - `X_±` is cocompact: `Λ` acts chamber-transitively and the Davis chamber is compact.
   - So by (FP) `X_±` is Gromov hyperbolic.
2. **A hyperbolic graph.** Let `G_±` be the 1-skeleton of a `Λ`-invariant subdivision of `X_±` into simplices with
   finitely many shapes, with unit edge lengths.
   - `G_±` is uniformly locally finite, again by finite thickness and finitely many shapes.
   - It is quasi-isometric to `X_±` [BH99, I.7, finitely many shapes], so it is Gromov hyperbolic.
   - `Λ` acts on `G_±` by graph automorphisms.
3. **Bounded orbits.** Every element of `E` has finite order, so it has finite, hence bounded, orbits on `G_±`. By
   (HO) Corollary B(2), `E` has a bounded orbit on `G_+` and one on `G_-`.
   - A bounded set of vertices in a locally finite graph is finite, so `E` has finite orbits on the vertices of `G_+`
     and of `G_-`.
   - Vertices are spherical residues, which have finitely many chambers. So a finite-index subgroup `E_1 ≤ E` fixes a
     chamber `c_+ ∈ Δ_+` and a chamber `c_- ∈ Δ_-`.
4. **Finite.** `Stab_Λ(c_+) ∩ Stab_Λ(c_-)` is finite: it is `T(F_q) · U_(Φ_+ ∩ wΦ_-)` after conjugation, as in
   `two-dim-cat0-product-groups-torsion-lf-proof`, Item 2. So `E_1` is finite, and so is `E`.
5. **`Λ/Z(Λ)`.** `Z(Λ)` is finite, so a finitely generated torsion subgroup of `Λ/Z(Λ)` has finite preimage.
6. **Item 2.** Combine with the Caprace–Rémy corollary (`simple-kazhdan-kac-moody-lattices-exist`). The rank-3
   example: the `(2,4,6)` triangle group acts cocompactly on the hyperbolic plane, so it is word-hyperbolic. ∎

## Remarks

- **Right-angled buildings.** The same argument with (HO) Corollary B(3), finite-dimensional CAT(0) cube complexes,
  handles Kac–Moody lattices whose Weyl group is right-angled, since right-angled buildings are CAT(0) cube complexes.
  Those groups are not 2-spherical, so they are not in the Caprace–Rémy finitely presented simple family. This is
  recorded only as a remark.
- **What would finish all Kac–Moody lattices.** Haettel–Osajda's conjecture for Davis realizations of buildings of any
  type: finite-dimensional CAT(0), locally finite, finitely many shapes.
