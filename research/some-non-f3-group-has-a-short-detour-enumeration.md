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
- A negative result would also be progress. Any invariant of groups with a
  short-detour enumeration that forces F_3 would show that the construction
  cannot refute Problem 1.3.
