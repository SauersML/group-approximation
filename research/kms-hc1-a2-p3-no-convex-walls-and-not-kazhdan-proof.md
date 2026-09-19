---
rg: 2
id: kms-hc1-a2-p3-no-convex-walls-and-not-kazhdan-proof
kind: route
title: GAP gives P_3 of index 3^6 with abelianization Z^24 + Z/3 and injective vertex groups, which refutes (T); link analysis turns a convex wall into an induced-matching edge cut of the Pappus graph, and exhaustive search finds none
target: kms-hc1-a2-p3-no-convex-walls-and-not-kazhdan
requires: [kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal, kms-hc1-a2-pro-p-completion-is-iwahori-criterion]
---

Notation is as in the claim. `E` is
`experiments/kms-hc1-a2-p3-median-walls-2026-09-19`.

## 1. The subgroup P_3

`E/not_t.g` builds `Gamma_3` from the presentation and calls
`EpimorphismPGroup(G,3,cl)` for `cl = 1, 2`. This gives the quotients by
`P_2` and `P_3` of the lower exponent-3 central series. For each, it prints
the abelian invariants of the kernel, computed by Reidemeister--Schreier
inside GAP. `E/not_t.out` records:

- `[Gamma_3 : P_2] = 3^3`, with `P_2^ab = (Z/3)^5`;
- `[Gamma_3 : P_3] = 3^6`, with `P_3^ab = Z^24 + Z/3`;
- each of `<a,b>`, `<b,c>`, `<c,a>` has image of order 27 in `Gamma_3/P_3`.

**Torsion-freeness.** `Gamma_3` acts properly on the complete CAT(0) space
`X_3`. So every finite subgroup `F` fixes a point (Bridson--Haefliger II.2.8)
and lies in a cell stabilizer. Stabilizers of triangles are trivial. Edge
stabilizers are conjugates of `<a>`, `<b>` or `<c>`, and these lie in the
vertex groups. So `F` lies in a conjugate of a vertex group. Those inject
into `Gamma_3/P_3`, and `P_3` is normal, so `F cap P_3 = 1`. Hence `P_3` is
torsion-free.

**The quotient Y.** `P_3` acts freely on the contractible complex `X_3`. So
`Y = X_3/P_3` is a compact aspherical, non-positively curved 2-complex with
`pi_1 = P_3`. Count cells:

- 3 vertex orbits with stabilizers of order 27, giving `3 * 3^6 / 27 = 81`
  vertices;
- 3 edge orbits with stabilizers of order 3, giving `3 * 3^6 / 3 = 729`
  edges;
- one free triangle orbit, giving 729 triangles.

So `chi(Y) = 81 - 729 + 729 = 81`. This matches `3^6 chi(Gamma_3)`, where
`chi(Gamma_3) = 3/27 - 3/3 + 1 = 1/9`. Over `Q`, `b_0 = 1` and `b_1 = rank P_3^ab = 24`,
so `b_2 = 81 - 1 + 24 = 104`.

## 2. Not (T)

- Property (T) passes to finite-index subgroups (Bekka--de la Harpe--Valette,
  Thm 1.7.1).
- A finitely generated group with (T) has finite abelianization (BdlHV,
  Cor. 1.3.6).
- `P_3` has abelianization `Z^24 + Z/3`, which is infinite. So `Gamma_3`
  does not have (T).
- Ozawa (J. Inst. Math. Jussieu 15 (2016)) shows that `Gamma` has (T) if and
  only if `Delta^2 - lambda Delta` is a sum of hermitian squares in `R[Gamma]`
  for some `lambda > 0`. So no such certificate exists at any radius.

`phi` maps `Gamma_3` onto `U_+` (target, part (K)). `U_+` has finite index in
`SL_3(F_3[t])`, which is a lattice in `SL_3(F_3((1/t)))`, so `U_+` is
Kazhdan. A non-Kazhdan group can have a Kazhdan quotient, so there is no
conflict.

## 3. No convex wall

Let `W` be a convex wall.

**(a) Cells meet W in segments.** A closed triangle `T` is convex in `X_3`:
the Euclidean segment in `T` between two of its points is a local geodesic,
hence a geodesic, since `X_3` is CAT(0). So `W cap T` is convex in `T`. It
has empty interior, so it is empty, a point, or a segment. Near any point
`p` of `W`, therefore, `W` is the cone over a finite set `S = S_p` of the
space of directions `Lk(p)`.

**(b) Angles.** Take `s != t` in `S`. Suppose their angle `min(pi, d_Lk(s,t))`
is `< pi`. Let `x`, `y` be the points at small distance `r` along `s` and `t`.
Since `X_3` is locally the Euclidean cone over `Lk(p)`, the geodesic `[x,y]`
misses `p`. It crosses the open sector between the two rays, which contains
no ray of the cone over `S`. But `[x,y]` lies in `W` by convexity, which is a
contradiction. So

```text
d_Lk(s,t) >= pi   for all s != t in S.
```

**(c) Local sides.** The components of `B(p,r) \ W` are the cones over the
components of `Lk(p) \ S`. Each one lies in `H+` or in `H-`.

**(d) Interior points of triangles.** Here `Lk(p)` is a circle of length
`2pi`. By (b), `|S| <= 2`. If `|S| = 1`, the complement is connected and `p`
touches only one side. So `S` is an antipodal pair, and `W` is locally a
straight segment. Its two local sides lie in different halfspaces, since `p`
is in the closure of both.

**(e) Interior points of edges.** `Lk(p)` is the theta graph: poles `xi+`,
`xi-` joined by 3 arcs of length `pi`.

- **Along the edge.** If `xi+` is in `S`, then by (b) the only other possible
  point is `xi-`.
  - `S = {xi+}` is impossible: `Lk \ {xi+}` is connected, so `p` would touch
    only one side.
  - So `S = {xi+, xi-}`, and `W` contains the edge near `p`.
  - The three open sectors (the three triangles at the edge) must then not
    all lie in the same halfspace.
- **Transverse.** Otherwise `S` lies in the open arcs.
  - Two points on the same arc are at distance `< pi`, so `S` has at most
    one point `theta_i` per arc, measured from `xi+`.
  - Removing points from fewer than 3 arcs leaves the theta graph connected,
    so all 3 arcs are hit.
  - For `i != j`, `d = min(theta_i + theta_j, 2pi - theta_i - theta_j) >= pi`
    forces `theta_i + theta_j = pi`. So every `theta_i = pi/2`: `W` crosses
    the edge perpendicularly in all three triangles.

**(f) Pieces in a triangle.** Let `W cap T` meet the interior of `T`. By (d)
it is a straight segment. Each endpoint is either a vertex, or an interior
edge point where the transverse case of (e) holds.

A segment in an equilateral triangle that is perpendicular to one side at an
interior point meets the other two sides at angle `pi/6`. So it ends at the
opposite vertex. Hence `W cap T` is one of:

- empty;
- an altitude, from a vertex to the midpoint of the opposite side;
- contained in `dT`, as a union of edges and points.

In all cases `W` contains a vertex `v`. At `v`, `S_v` is a subset of the
Pappus link `L`, which has edges of length `pi/3`. It is the union of:

- a set `A` of link **vertices**, the edges of `X_3` in `W`;
- a set `M` of link-edge **midpoints**, the altitudes in `W`.

`S_v` is nonempty, since otherwise `v` is isolated in `W` and touches only
one side.

**(g) Local conditions at v.** For link points we have

```text
d_L(m_e, m_f) = pi/3 + (pi/3) * min{ d_L(x,y) : x in e, y in f }    (e != f),
d_L(a,   m_e) = pi/6 + (pi/3) * min{ d_L(a,y) : y in e }.
```

So (b) says:

- two vertices of `A` are at graph distance `>= 3`;
- a vertex of `A` and an edge of `M` are at minimum endpoint distance `>= 3`;
- two edges of `M` are at minimum endpoint distance `>= 2`.

Colour each component of `L \ S_v` by its halfspace, using (c).

- Points of `W` near `v` on an altitude have their two local sides in
  different halfspaces, by (d). So the two ends of every edge of `M` get
  different colours.
- Points near `v` on an edge of `A` have, by (e), their three sectors not all
  in one halfspace. So the three neighbours of each `a` in `A` do not all get
  the same colour.

If `A` is empty, the conditions say that `S_v = M` is the edge cut of a
bipartition of `V(L)` and is an induced matching. These are conditions (C1)
and (C3) of `E/pappus_cuts.py`.

**(h) Enumeration.** `E/pappus_cuts.py` builds `L` as the coset graph of the
Heisenberg group of order 27, and asserts 18 vertices, 27 edges and
valency 3.

- **Midpoint shapes.** It runs through all `2^17 - 1` nontrivial
  bipartitions, fixing the last vertex in `Q`. It finds **0** satisfying
  (C1) and (C3).
- **General shapes.** It lists every nonempty `S = A u M` satisfying the
  distance conditions of (g), 1293 in all, by backtracking over the 45
  points. For each, it tries every 2-colouring of the components of
  `L \ S`. **None** meets the colour conditions (`E/pappus_cuts.out`).
- **Negative control.** Lowering the thresholds to 2/2/1 makes the same code
  find 2555 admissible sets out of 99911. This was run on a scratch copy and
  is not shipped.

This contradicts (g), so no convex wall exists.

The same run also computes the bend profile of the 10125 midpoint
bipartitions with connected `P` and `Q`. The minimum median angle is `pi/3`
for 10080 of them and `2pi/3` for 45. The fewest pairs at angle `< pi` is 3,
attained by `P` = one vertex.

## 4. The kernel of phi^ is infinite

- **Open subgroups of I_1 have finite abelianization.** Let `K_m` be the
  level-`m` congruence subgroup of `SL_3(F_3[[t]])`. Then
  `K_j/K_(j+1) = sl_3(F_3)`, and the elements `x_ik(t^j)` and
  `diag(1+t^j, (1+t^j)^-1, 1)` realize all leading terms.
- If `x` is in `K_m` and `y` is in `K_n`, the commutator `[x,y]` is
  congruent to `1 + t^(m+n)[A,B]` mod `t^(m+n+1)`. Here `A` and `B` are the
  leading terms of `x` and `y`.
- `sl_3(F_3)` is perfect. `[e_ij, e_jk] = e_ik` and `[e_ij, e_ji] = e_ii - e_jj`
  span all 8 dimensions, including the scalars, since `3 = 0`.
- So the closed subgroup `C = [K_m, K_m]` satisfies `C K_(j+1) >= K_j` for
  every `j >= 2m`. By completeness, `C >= K_2m`.
- Every open subgroup `H` of `I_1` contains some `K_m`. So `H^ab` is a
  quotient of `H/K_2m`, which is finite.
- **The pro-3 side.** `P_3` is normal of 3-power index. So its closure
  `bar P_3` in `Gamma_3^` is its own pro-3 completion. Every 3-power-index
  normal subgroup of `P_3` contains its `Gamma_3`-core, and that core has
  3-power index in `Gamma_3`. Hence
  `bar P_3^ab = (P_3^ab)^_3 = Z_3^24 + Z/3`.
- `|Gamma_3/P_3| = 3^6 = |I_1/P_3(I_1)|` (target, (T3)). So `phi^` induces
  an isomorphism modulo `P_3`, and `ker phi^ <= bar P_3`.
- `phi^(bar P_3) = P_3(I_1)` is open, so it has finite abelianization. So the
  image of `ker phi^` in `bar P_3^ab` has finite index.
- Therefore `ker phi^` surjects onto a finite-index subgroup of
  `Z_3^24 + Z/3`. In particular it is infinite.

## 5. Codimension-1 subgroups survive

- Take a surjection `f: P_3 -> Z`. Its kernel `N` has `e(P_3, N) = 2`.
- By Sageev (Proc. LMS 71 (1995)), `P_3` then acts on a CAT(0) cube complex
  without a global fixed point. Inducing up gives such an action of
  `Gamma_3` as well. This does not conflict with part 2.
- These `N` are infinite-index normal subgroups, so they are not
  quasiconvex. A proper cocompact cubulation still needs relatively
  quasiconvex codimension-1 subgroups.
- By section 3, the tracks of such subgroups in `X_3` cannot be convex. Every
  locally two-sided track bends at a vertex by at least `pi/3`.
