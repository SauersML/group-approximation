---
rg: 2
id: product-of-two-trees-lattices-pbh-proof
kind: route
title: Split a product-of-trees lattice along one tree into a graph of virtually free groups with finite-index edges
target: product-of-two-trees-lattices-satisfy-permutational-boone-higman
requires: [free-generalized-bs-groups-have-type-a-overgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation is as in the target. `Gamma_0` is the kernel of the homomorphism
`Gamma -> Z/2` recording whether the factors are swapped, so
`[Gamma : Gamma_0] <= 2`. Swapping is only possible when `T_1 ≅ T_2`, in which
case both trees have more than two ends. So we may assume `T_2` has more than
two ends. Every stabilizer below is taken in `Gamma_0`. The two coordinate
actions are written `gamma v` and `gamma w`.

**Step 1 (removing inversions).** Let `T_1'` be the barycentric subdivision of
`T_1`, on which `Gamma_0` acts without inversions.
- The vertices of `T_1'` are the vertices `v` of `T_1` and the midpoints `m_e`
  of edges `e`.
- `Gamma_(m_e)` is the setwise stabilizer of `e`.
- The edges of `T_1'` are the pairs `{v, m_e}` with `v ∈ e`. Their stabilizer
  is the pointwise stabilizer `Gamma_e = Gamma_v ∩ Gamma_(m_e)`.

**Step 2 (finite quotient).** `Gamma_0` has finite index in `Gamma`, so it has
finitely many orbits on `V(T_1) x V(T_2)`, and hence on `V(T_1)`. Each edge of
`T_1` has an endpoint in one of finitely many orbit representatives, each of
finite degree. So the edges also fall into finitely many orbits, and
`Y = Gamma_0 \ T_1'` is a finite graph.

**Step 3 (Bass--Serre).** `Gamma_0` is the fundamental group of a graph of
groups over `Y` whose vertex groups are the stabilizers `Gamma_x` of vertex
representatives, whose edge groups are the stabilizers `Gamma_e`, and whose
edge maps are inclusions up to conjugation. This is the structure theorem for
actions on trees without inversions (Serre, *Trees*, §I.5.4; not re-read).

**Step 4 (finite-index edges).**
- `Gamma_v / Gamma_e` is in bijection with the `Gamma_v`-orbit of `e` among the
  edges at `v`, so `[Gamma_v : Gamma_e] <= deg(v)`.
- `[Gamma_(m_e) : Gamma_e] <= 2`, since `Gamma_(m_e)` permutes the two endpoints
  of `e`.

**Step 5 (the vertex groups act geometrically on `T_2`).**
- **Finite stabilizers.** For `w ∈ V(T_2)`, the stabilizer of `w` in `Gamma_v`
  is the stabilizer of `(v,w)`, which is finite. For `x = m_e`, the stabilizer
  of `w` in `Gamma_e` fixes `(v,w)`, and it has index at most 2 in the
  stabilizer of `w` in `Gamma_(m_e)`. So both are finite.
- **Finitely many orbits.** If `gamma (v,w) = (v,w')` then `gamma ∈ Gamma_v`. So
  `[w] ↦ [(v,w)]` injects `Gamma_v \ V(T_2)` into the finite set
  `Gamma_0 \ (V(T_1) x V(T_2))`. Finite-index subgroups and overgroups of
  `Gamma_v` also have finitely many orbits, so this covers `Gamma_e` and
  `Gamma_(m_e)`.

**Step 6 (virtually free).** Subdivide `T_2` so that `Gamma_x` acts without
inversions; midpoint stabilizers are still finite.
- By Step 5 and the structure theorem, `Gamma_x` is the fundamental group of a
  finite graph of finite groups.
- Such a group is finitely generated and virtually free (Serre, *Trees*, §II.2.6;
  Karrass--Pietrowski--Solitar; not re-read).

**Step 7 (not virtually cyclic).** Suppose `Gamma_x` is virtually cyclic.
- **Finite case.** If `Gamma_x` is finite, then finitely many finite orbits
  cover `V(T_2)`. So `T_2` is finite and has no ends.
- **Infinite case: `g` is hyperbolic.** Otherwise pick `g ∈ Gamma_x` of infinite
  order with `<g>` of finite index. If `g` were elliptic, then `g^2` would fix a
  vertex of the subdivided tree. Then `g^2` would lie in a finite stabilizer,
  although it has infinite order. So `g` is hyperbolic, with an axis `A`.
- **`T_2` is close to the axis.** `d(-, A)` is constant on `<g>`-orbits, and
  `<g>` has finitely many orbits on vertices. So every vertex lies within some
  fixed distance `D` of `A`.
- **At most two ends.** A geodesic ray within distance `D` of the line `A` shares
  a subray with `A`. So `T_2` has at most the two ends of `A`.

Both cases contradict the hypothesis, so `Gamma_x` is not virtually cyclic.

**Step 8 (commensurable with `F_2`).**
- By Step 6, `Gamma_x` contains a free subgroup `F` of finite index. `F` is
  finitely generated, of rank `r`.
- `r >= 2`: rank at most 1 would make `Gamma_x` virtually cyclic, against Step 7.
- By the Nielsen--Schreier index formula, a subgroup of index `r - 1` in `F_2`
  is free of rank `r`, so `F` is a common finite-index subgroup of `Gamma_x` and
  `F_2`.
- By Step 4, each edge group has finite index in a vertex group, so it is
  commensurable with `F_2` as well.

**Step 9 (conclusion).**
- **Membership.** By Steps 2, 3, 4 and 8, `Gamma_0` is the fundamental group of
  a finite graph of groups whose vertex and edge groups are abstractly
  commensurable with `F_2`, with all edge inclusions of finite index. That is,
  `Gamma_0 ∈ BS_(F_2)` in the definition quoted in
  `free-generalized-bs-groups-have-type-a-overgroups`.
- **Type (A).** That claim gives `Gamma_0 ∈ B_A`. Items 1 and 2 of
  `boone-higman-type-a-class-closed-under-finite-extensions` pass this to
  `Gamma ⊇ Gamma_0`, and to every subgroup of `Gamma`.
- **Envelopes.** Item 3 of the same claim gives a finitely presented simple
  envelope for each subgroup, and solvable word problem for the finitely
  generated ones. `∎`
