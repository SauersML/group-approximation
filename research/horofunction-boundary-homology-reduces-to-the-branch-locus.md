---
rg: 2
id: horofunction-boundary-homology-reduces-to-the-branch-locus
kind: claim
title: For a torsion-free hyperbolic group, the cohomology of G with coefficients in C(∂_h G, Q) is the leftmost column of a descent spectral sequence over the branch locus of ∂_h G → ∂G that converges to the cohomology of the Gromov-boundary suspension; for sphere boundaries of dimension m >= 2 that branch locus has dimension >= m-1
distinct_from:
  bbmz-host-finiteness-reduces-to-the-vertex-boundary-groupoid: that turns F_n of the BBMZ host into finite-dimensionality of H_k(G; C(∂_h G, Q)); this reduces that finite-dimensionality to the branch locus of ∂_h G → ∂G, and shows that for Kazhdan Sp(n,1) lattices it is a (4n−2)-dimensional tiling-cohomology problem.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-18; not reviewed).
- The ingredients are standard: cohomological descent for proper surjections, the Leray
  spectral sequence, and the sum theorem of dimension theory.
- The finite-to-one map `φ : ∂_h G → ∂G` is Webster–Winchester's, as cited in BBMZ
  arXiv:2309.06224, §4.1.
- No computation was run. The task asked for one explicit Sp(n,1) lattice. None is available
  with an automatic structure, atom data or a finite K(G,1) that could be used, and the
  coefficient module is infinite-dimensional, so a bounded search cannot certify a dimension.
  Item 3 shows why no such search could settle the question.

## Setting

- **The group.** `G` is torsion-free and hyperbolic, with finite generating set `S`.
- **Two boundaries.** `X = ∂_h G` is the horofunction boundary for `S`, and `Z = ∂G` is the
  Gromov boundary.
- **The comparison map.** `φ : X → Z` is the continuous, surjective, `G`-equivariant,
  finite-to-one quotient map.
- **A model space.** `P` is a contractible, free and cocompact `G`-complex: the Rips complex, or
  `M̃` when `G = π_1(M)` for a closed aspherical manifold `M`.
- **Fiber products.** `X^{[p]} = X ×_Z ⋯ ×_Z X` (`p+1` factors). `X^{[p]}_≠` is the open subset
  of tuples with distinct entries. `C_c(·, Q)^±` denotes the alternating (sign-twisted
  `S_{p+1}`-invariant) locally constant functions with compact support.
- **The branch locus.** `B = {z ∈ Z : |φ^{-1}(z)| ≥ 2}`.

## Theorem

1. **Descent spectral sequence.** There is a first-quadrant spectral sequence

       E_1^{p,q} = H^q(G; C_c(X^{[p]}_≠, Q)^±)  ⟹  Ȟ^{p+q}(P ×_G Z; Q),

   with `X^{[0]}_≠ = X`. So its column `p = 0` is `H^q(G; C(∂_h G, Q))`. The columns `p ≥ 1` live
   over `B`, since `φ(pr_0(X^{[p]}_≠)) ⊆ B`.
2. **Finiteness criterion.** Suppose `Ȟ^*(P ×_G Z; Q)` is finite-dimensional in each degree, and
   `H^q(G; C_c(X^{[p]}_≠, Q)^±)` is finite-dimensional for all `p ≥ 1` and `q`. Then
   `H^q(G; C(∂_h G, Q))` is finite-dimensional for every `q`.
   - When `G = π_1(M)` with `M` closed and hyperbolic, `P ×_G Z = T^1 M`, so the first
     hypothesis holds.
   - Under Poincaré duality the conclusion gives the finite-dimensionality test of the parent
     node in every degree.
3. **The branch locus is large.**
   - `Z ∖ B` is totally disconnected, and `φ` restricts to a homeomorphism `φ^{-1}(Z ∖ B) → Z ∖ B`.
   - If `Z ≅ S^m` with `m ≥ 2`, then `B` is dense and uncountable, and `dim B ≥ m − 1`.
   - For a torsion-free cocompact lattice in `Sp(n,1)` (`m = 4n − 1`), `dim B ≥ 4n − 2`.
   - For surface groups (`m = 1`) a countable dense `B` is allowed.

## Proofs

**1.**
- **The augmented complex.** Let `U = P ×_G X → E = P ×_G Z` be the induced map. It is a proper
  surjection of compact spaces, and its Čech nerve is `U_p = P ×_G X^{[p]}`.
- **Exactness.** The alternating Čech complex `Q_E → π_*Q_{U_0} → π_*(Q^±_{U_1}) → ⋯` is exact.
  By proper base change, its stalk at a point with fiber `F` is the alternating cochain complex
  of the full simplex on the finite set `F`, which is acyclic.
- **The `E_1` page.** The alternating part of `C(X^{[p]}, Q)` vanishes on the partial
  diagonals. Its support is a clopen set disjoint from the closed diagonals, hence a compact
  subset of `X^{[p]}_≠`. So the `p`-th term has global sections `C_c(X^{[p]}_≠, Q)^±` fiberwise
  over `P / G`.
- **Leray.** `U_p → P/G` is a bundle with totally disconnected fibre `X^{[p]}`, and `P` is
  contractible. So `Ȟ^q(U_p; ·) = H^q(G; C_c(X^{[p]}_≠, Q)^±)`, and the higher direct images
  vanish.
- The spectral sequence is the standard descent spectral sequence of this resolution.

**2.**
- The differentials `d_r` go from column `p` to column `p + r`. So nothing enters column 0, and
  `E_∞^{0,q} = E_{q+2}^{0,q}` is reached after finitely many steps.
- Each step replaces `E_r^{0,q}` by the kernel of a map into a finite-dimensional group. So
  `E_∞^{0,q}` has finite codimension in `E_1^{0,q}`.
- `E_∞^{0,q}` is a subquotient of the finite-dimensional group `Ȟ^q(E; Q)`. Hence `E_1^{0,q}` is
  finite-dimensional.

**3.**
- Put `V = φ^{-1}(Z ∖ B)`. It is saturated, so `φ|_V : V → Z ∖ B` is a closed continuous
  bijection, hence a homeomorphism. Since `V ⊆ X` is totally disconnected, so is `Z ∖ B`.
- **`m ≥ 2`.**
  - The complement of a countable set in `S^m` is connected, so `B` is uncountable.
  - `B` is dense, since otherwise `Z ∖ B` would contain an open ball.
  - `Z ∖ B` has dimension 0, and the sum theorem gives `m ≤ dim B + dim(Z ∖ B) + 1`. So
    `dim B ≥ m − 1`.

## Consequence for the parent test

- **Sp(n,1) lattices.** For `G` a torsion-free cocompact lattice in `Sp(n,1)` (Kazhdan, PD(4n)),
  the parent node needs `H^j(G; C(∂_h G, Q))` for `1 ≤ j ≤ 4n − 2`. By item 1, this is controlled
  by `H^*(T^1M; Q)` together with the `G`-cohomology of locally constant functions on fiber
  products over a branch locus of dimension at least `4n − 2`.
- **What kind of problem this is.** It is a tiling-cohomology problem of Anderson–Putnam type,
  in dimension at least `4n − 2`.
- **Likely outcome.** The atom types are finite in number: BBMZ `prop:fin_many_types`, and the
  contracting lemma localizes intersections of shadows. That is the finite-type situation in
  which tiling cohomology is finite-dimensional. So the likely outcome is that the test
  **passes** and the homological obstruction is void. This is an expectation, not a claim.

## Lesson for general BH

- **Homology of a Cantor model is controlled by the branch locus.** For any Cantor model
  `∂_h G → ∂G` of a boundary action, the cohomology with locally constant coefficients is
  determined by its branch locus, through descent to the Gromov boundary.
- **The branch locus of a sphere is a wall.** When the boundary is a sphere of dimension
  `m ≥ 2`, the branch locus has dimension at least `m − 1`: coding a sphere by a Cantor set
  forces codimension-one walls. For finite-type codings, like the atom types of hyperbolic
  groups, this is the finite-type tiling situation, so homological obstructions to F_∞ of
  horofunction full groups are expected to vanish.
- **Where F_∞ gets decided.** For hyperbolic inputs, F_∞ of the BBMZ host is then decided by
  geometry: a Brown or germ-complex argument with non-atomic singular loci. The cheap homological
  test is not expected to rule it out, and no bounded computation can decide it.

## Next

- **Make the finite-type statement precise.** Show that the fiber products `X^{[p]}_≠` carry
  finitely many "atom-configuration types" up to `G` and level shift. Then run the
  Anderson–Putnam argument inductively on `p`. That would prove the test passes for every closed
  hyperbolic manifold group.
- **Return to the germ theorem.** The live F_∞ gate is a finite germ extension theorem for
  non-atomic singular loci (parent node, final section).
