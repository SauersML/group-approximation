---
rg: 2
id: some-non-f3-group-has-a-short-detour-enumeration
kind: claim
title: Some finitely presented group that is not of type F_3 has a short-detour enumeration
---

Some finitely generated group G that is not of type F_3 has a short-detour
enumeration, in the sense of
`short-detour-enumeration-gives-contractible-qi-2-complex`, with respect to
some finite generating set.

Such a G is automatically finitely presented. By that theorem it is
quasi-isometric to a contractible proper geodesic 2-complex, so it answers
Zaremsky Problem 1.3 negatively under the geodesic reading.

## Attempts

- Almost convex groups (Cannon) have short-detour enumerations
  (breadth-first order). The first question is whether a known almost convex
  group fails to be of type F_3, or whether almost convexity is known to
  imply F_3 or F_∞. Literature check pending (lane z1-03-qi-fn, 2026-09-13).
- Test cases:
  - the Stallings–Bieri group SB_3 = ker(F_2^3 → Z), the Bestvina–Brady group
    of the octahedron;
  - Houghton's group H_3;
  - more generally Bestvina–Brady groups BB_L with L a flag 2-sphere.

  In each case look for an exhaustion of the level set (vertices of height 0
  in the cube complex of A_L) that never merges two regions far apart in
  the induced graph. The obstacle is a vertex whose neighbours sit on
  opposite sides of a not-yet-filled octahedral shadow.
- Second test case, the double D = F_2^2 *_{SB_2} F_2^2 (two copies of F_2 × F_2
  glued along the Stallings–Bieri subgroup SB_2 = ker(F_2^2 → Z)).
  - D is finitely presented, since it is an amalgam of finitely presented
    groups over a finitely generated subgroup.
  - D is not of type FP_3. Tree Mayer–Vietoris gives
    0 → Z[D] ⊗_{SB_2} Z → Z[D] ⊗_H Z ⊕ Z[D] ⊗_{H'} Z → Z → 0, where the middle
    term is FP_∞. Bieri's lemma then gives: D is FP_3 iff SB_2 is FP_2, and
    SB_2 is not.
  - Local structure: a vertex v lies in one H-coset and one H'-coset.
    Neighbours v·a_1 ∈ vH and v·a'_1 ∈ vH' have the common neighbour
    v·a_1 a_2^{-1} = v·a'_1 a'_2^{-1} in the SB_2-coset. So the enumeration
    must add that edge-space point before v whenever it uses both cosets.
    Plan: grow product boxes of trees in each vertex space. The two sides must
    agree on the added part of each SB_2-coset (same subgroup, same metric).
- A negative result would also be progress. Any invariant of groups with a
  short-detour enumeration that forces F_3 would show that the construction
  cannot refute Problem 1.3.
