---
rg: 2
id: cat0-cube-complexes-have-the-jensen-helly-property-proof
kind: route
title: Vertex distances are affine on the hyperplane box, and unfolding charged empty quadrants retracts the box onto the cube complex
target: cat0-cube-complexes-have-the-jensen-helly-property
requires: []
artifacts:
  - research/artifacts/zp-cube-complex-jensen-helly-2026-09-16.md
---

Direct proof; full details are in the artifact (§§1–8). It uses only standard
median-graph facts:
- halfspaces are convex;
- `d` counts separating hyperplanes;
- convex sets are gated;
- convex sets have Helly number 2, proved there via medians.

Notation. For `p ∈ [0,1]^H` the charge on a halfspace `A` of `h` is `p_h` or
`1 − p_h`. For a vertex `x`, `d_1(x,p) = L_x(p)` = the total charge on the
halfspaces not containing `x`, an affine function on the whole box. For
`w_h = μ(h^1)` this gives `L_x(w) = ∫ d(x,y) dμ`.

1. **Lemma C.** Let `G` be finite. Then `p ∈ |X|` iff no *empty quadrant* is
   charged. An empty quadrant is a pair of halfspaces `A`, `B` of distinct
   hyperplanes with `A ∩ B = ∅`; charged means `q_A(p) > 0` and `q_B(p) > 0`.
   - (⇒) Check the corners of the cube.
   - (⇐) For each sign pattern `σ` on the fractional coordinates, the chosen
     halfspaces pairwise meet. Helly number 2 gives a unique vertex `v_σ`, and
     these vertices form a coordinate cube containing `p`.
2. **Lemma U (unfolding).** Suppose `(A,B)` is charged, and let `s` be the
   smaller of the two charges. Move charge `s` off `A` and off `B`. Then every
   `L_x` stays the same, except that it drops by `2s` on `A* ∩ B*`, which is
   nonempty because distinct hyperplanes have distinct splits.
3. **Lemma J.** Take `G` finite. Minimize `Σ_x L_x` over the polytope
   `{c ∈ [0,1]^H : L_x(c) ≤ L_x(w) ∀x}`. A charged quadrant at a minimizer
   could be unfolded, so by Lemma C the minimizer lies in `|X|`. For infinite
   `G`, work in the finite hull of `supp μ` and extend through gates.
4. **Lemma Rt.** Let `r(c)` be the unique minimizer of
   `Σ_x L_x + (1/8) Σ_h c_h²` over `D_c = {c' : L_x(c') ≤ L_x(c) ∀x}`.
   - `r(c) ∈ |X|`: an unfolding lowers the objective.
   - `r` fixes `|X|`: adding antipodal corner inequalities, then comparing
     adjacent corners, gives `D_p = {p}`.
   - `r` is continuous, by Hoffman's error bound and uniqueness.
   So each nonempty intersection of vertex-centred balls `B_I` is a retract of
   a convex polytope `P_I`, hence contractible.
5. **Lemma H.** Triangulate `|X|` so that every ball is a subcomplex; the
   triangulation has dimension `≤ k`. A minimal non-meeting family
   `B_0..B_n` has `n ≥ k+1`, and by the nerve theorem its union `U` is
   homotopy equivalent to `S^{n−1}`.
   - If `n − 1 > k`: `H^{n−1}(U) = 0` by dimension, a contradiction.
   - If `n − 1 = k`: `0 = H^k(|X|) → H^k(U) → H^{k+1}(|X|,U) = 0`, a
     contradiction.
   For infinite `G`, pass to the hull of the centres and the corners of the
   witness cubes.
6. **Lemma R.** Round the fractional coordinates.

**Trust surface (standard results used without proof, not re-fetched).**
- Median graphs (Mulder 1980; Bandelt–Chepoi survey 2008): Θ is an
  equivalence relation whose classes cut `G` into two convex halfspaces, `d`
  counts separating hyperplanes, convex sets are gated, and convex subgraphs
  are median with the traced hyperplanes (artifact §1, (M1)–(M4)).
- Hoffman's error bound for linear inequality systems (J. Res. Nat. Bur.
  Standards 49 (1952) 263–265), used only for continuity of `r`.
- The nerve theorem for a finite simplicial complex covered by subcomplexes
  with contractible intersections (Björner, *Topological methods*, Handbook
  of Combinatorics, 1995, Theorem 10.6), plus polyhedral subdivision and the
  long exact sequence of a pair in simplicial cohomology.
Everything else (Helly number 2 for convex sets, Lemmas C, U, J, Rt, H, R)
is proved in the artifact.

Cross-checked with linear programs over hulls of random vertex sets in
Salvetti covers of `P4`, `C5`, `K_1*P4` and `K_2*P4`, and over arbitrary
split systems (experiments/zaremsky-4-05-jensen-cube-2026-09-16):
- the box minimum equals the complex minimum;
- LP minimizers have no charged quadrant;
- no Helly-number-`(k+1)` failures were found, while the same search finds
  failures for `k` members.
