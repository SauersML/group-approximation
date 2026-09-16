---
rg: 2
id: some-planar-rips-chain-gadget-multiplies-a-sphere-class
kind: claim
title: "Some finite planar set carries a translation chain gadget whose port class is a multiple, by a factor of absolute value at least two, of the translated port class"
distinct_from:
  some-infinite-planar-set-has-a-non-wedge-rips-complex: that claim asks for any infinite counterexample; this one asks for a specific finite local configuration which, by the route infinite-non-wedge-from-a-multiplying-chain-gadget, yields one
  some-finite-planar-set-has-a-non-wedge-rips-complex: that claim asks for a finite non-wedge; a gadget is known to give a finite non-wedge when its port is coneable, and a finite non-wedge need not give a gadget
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

There exist:

- a finite set `G ⊆ R^2` and a scale `r > 0` (closed convention:
  simplices have diameter `≤ r`);
- a vector `v ≠ 0`, with translation `τ(x) = x + v`;
- a subset `A ⊆ G`, a class `z ∈ H_2(R_r(A); Z)`, and an integer `m` with
  `|m| ≥ 2`,

such that, with `B = τ(A)`, inclusions `i_A : R(A) → R(G)` and
`i_B : R(B) → R(G)`, and `τ_* : H_2(R(A)) → H_2(R(B))`, the following hold.

- (G0) `R_r(G)` is connected.
- (G1) `B ⊆ G` and `A ∩ B = ∅`.
- (G2) *Separation.* If `x ∈ G ∖ B`, `y ∈ τ^k(G)` with `k ≥ 1`, and
  `|x − y| ≤ r`, then `k = 1` and `y ∈ B`. This is a finite check, since it
  is automatic once `|kv| > diam G + r`.
- (G3) `ker(i_{A*} : H_2(R(A)) → H_2(R(G)))` is a torsion group.
- (G4) `a = i_{A*}(z)` has infinite order and `a = m · i_{B*}(τ_* z)` in
  `H_2(R_r(G))`.

Route `infinite-non-wedge-from-a-multiplying-chain-gadget` proves that such a
gadget gives an infinite planar set `X = ∪_{k ≥ 0} τ^k(G)`. Its Rips complex
is connected, and `H_2` contains a nonzero element divisible by every power of
`m`. So `H_2` is not free, and the complex is not a wedge of spheres, in
either convention.

## Attempts

All proofs are in
`research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §4
and §7.

- **Relative torsion is forced (§4.1).** If `H_2(R(A)) = Z z`, for example an
  octahedral hexagon, then (G4) forces torsion of order dividing `m` in
  `coker(i_{A*})`. Hence there is torsion in
  `H_2(R(G), R(A)) ≅ H_2(R(G) ∪ cone R(A))`, a flag complex: the `r`-graph on
  `G` plus one vertex joined to `A`. With a rank-one port, a gadget is a
  non-pure image of `H_2(R(A))`. Torsion searches on `R(G)` alone cannot see
  it.
- **Any port rank (§4.1′, referee addition).** If `H_2(R(A))` is torsion-free,
  of any rank, (G3)–(G4) still force a nonzero element of order dividing `m`
  in `coker(i_{A*})`. Otherwise the iteration `z = m^k w_k` makes `z`
  infinitely divisible in a free group. If `H_2(R(A))` has torsion, some
  component of `R(A)` is already a finite non-wedge.
- **A coneable port settles the finite question (§4.2).** Suppose some point
  `p` has `{g ∈ G : |g − p| ≤ r} = A`. Then `R(G ∪ {p})` is finite and
  connected, and `H_2(R(G ∪ {p})) ⊇ coker(i_{A*})`. By §4.1′ this has torsion
  whenever `H_2(R(A))` is torsion-free, and otherwise a component of `R(A)`
  has torsion in `H_2`. Either way
  `some-finite-planar-set-has-a-non-wedge-rips-complex` would follow. So a
  gadget is new for the infinite question only if its port is not coneable.
- **One-point extensions keep images pure (§4.3).** Adding one point `w`
  makes `H_2(R(F))` pure in `H_2(R(F ∪ {w}))`, because the quotient embeds in
  the free group `H_1(R(N(w) ∩ F))`. Purity is not preserved under
  composition, so non-purity has to come from several points acting together.
- **Sliding gives `m = ±1` (§4.4).** Moving one vertex of an octahedral sphere
  to a point within `r` of it, with the octahedron preserved, changes the class
  only by the boundary `∂((a_1 a_1′) * L)`. Tracks of octahedra carry `a` to
  `±b`, never to a proper multiple.
- **The pants mechanism is not planar (§4.6).** The flag complex
  `S^0 * S^0 * Ind(K_3)` has the octahedron relation `O_13 = O_12 + O_23`,
  which together with a slide would give `m = 2`. It is not planar: for any
  far pair `a, a′`, the far graph on `N(a) ∩ N(a′)` is bipartite, split by the
  line `aa′`. The proof uses crossing diagonals of a convex quadrilateral. So
  there are never five points with far graph `K_2 ⊔ K_3` and all cross pairs
  near. The `far_k2_k3_search.py` hill-climbing check found only negative
  slack, about `−7 · 10^{−5}` at best.
- **Computation (§7).** A search over 24,000 relative complexes detected no
  2- or 3-torsion; other primes were not tested. The complexes were: clique
  complex of the `r`-graph on `G` plus a cone vertex on `A`, reduced by
  dominated vertices and edges, with Betti numbers mod 2 and mod 3 compared
  against those mod 1000003. The families were hexagon plus
  random points, two hexagons in a strip (one or both as the port), disks and
  half-planes. Nontrivial relative `H_2` was common (e.g. 1420 of 1970 in one
  run), and no mod-2 or mod-3 Betti jump occurred. The script and output are in
  `experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/`.
- **Relation to Attempt (B) of the finite claim.** That attempt needs the same
  local multiplicity relation between neighbouring spheres and then closes the
  chain by a rotation. Its obstacle applies here unchanged: carrying a sphere
  needs steps below `r`, while separation needs steps above `r`.
- **Still open.** Nothing above rules out non-octahedral port classes (e.g.
  `H_2(R(A))` of rank `≥ 2`), or multiplicities that arise from sums over
  several tracks.
