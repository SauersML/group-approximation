---
rg: 2
id: sl3z-racg-witnesses-are-antiflag-configurations
kind: claim
title: Right-angled Coxeter subgroups of GL_3(Z) are integral anti-flag configurations with forced shared-centre rules
distinct_from:
  sl3z-contains-rfrs-cd2-subgroup-with-positive-b2: that is the existence target for any virtually RFRS cd-two subgroup; this is a normal form and necessary conditions for the right-angled Coxeter candidates for it
  two-dimensional-coxeter-coherence-criterion: that decides coherence of an abstract Coxeter group; this decides which right-angled Coxeter groups can sit faithfully inside GL_3(Z), and how
  sl3r-simply-connected-domain-subgroups-are-coherent: that forbids convex-domain certificates of faithfulness; this gives the combinatorial normal form any faithful embedding must take
artifacts:
  - experiments/sl3z-racg-realization-2026-09-17/antiflag.py
  - experiments/sl3z-racg-realization-2026-09-17/kernel.py
  - experiments/sl3z-racg-realization-2026-09-17/round5.py
  - experiments/sl3z-racg-realization-2026-09-17/orbits.py
  - experiments/sl3z-racg-realization-2026-09-17/exact.py
  - experiments/sl3z-racg-realization-2026-09-17/RESULTS.md
---

Let `Gamma` be a finite simplicial graph in which no vertex is adjacent to all
the others, and let `W = W_Gamma` be its right-angled Coxeter group, with
generators `s_v`. Let `rho : W -> GL_3(Z)` be injective.

**(A) Normal form.** There is a character `eps : W -> {±1}` such that
`rho' = eps rho` is still injective and, for every vertex `v`,

`rho'(s_v) = I - (2/d_v) p_v L_v^T`,

where:

- `p_v` and `L_v` are primitive vectors in `Z^3`, each determined up to a
  common sign;
- `d_v = L_v · p_v` lies in `{1, 2}`;
- the centre `[p_v]` is a point of `RP^2`, the axis `[L_v]` is a line, and
  `[p_v]` does not lie on `[L_v]`.

Write `a_uv = 2 L_u·p_v / d_u` for the Cartan entries. Then:

- (A1) distinct vertices give distinct anti-flags `([p_v],[L_v])`;
- (A2) `u ~ v` if and only if `L_u·p_v = L_v·p_u = 0` (mutual incidence);
- (A3) if `u` and `v` are not adjacent, then `a_uv a_vu` is not in
  `{1, 2, 3}`, and `a_uv`, `a_vu` are not both `0`.

Conversely, a family of integral anti-flags satisfying (A2) and (A3) defines
a homomorphism `W -> GL_3(Z)`. Suppose moreover that `Gamma` is triangle-free
and has an induced subgraph `Lambda`, not a complete graph (so `W_Lambda` is
infinite), with `chi(W_Lambda) = 1 - V/2 + E/4 > 0`.
If that homomorphism is injective, then `SL_3(Z)` is incoherent, by
`two-dimensional-coxeter-coherence-criterion`: its intersection with
`SL_3(Z)` has index at most two.

**(B) Forced rules** for an injective `rho'` in normal form:

- (R1) No three vertices share a centre, and no three share an axis.
- (R2) Suppose `u != w` are two vertices with a common centre `p`. Then every
  other vertex `x` whose axis passes through `p` is adjacent to both `u` and
  `w`.
- (R3) Dually, suppose `u != w` have a common axis `L`. Then every other
  vertex `x` whose centre lies on `L` is adjacent to both `u` and `w`.
- (R4) Take an induced 4-cycle `v – u_1 – w – u_2 – v`. Exactly one of the
  following holds:
  - the centres coincide in pairs, `p_{u_1} = p_{u_2} = p` and
    `p_v = p_w = q`. Then `s_{u_1} s_{u_2}` and `s_v s_w` are transvections
    with the common axis `pq`, and they generate a rank-two subgroup of the
    abelian group of transvections with that axis;
  - the axes coincide in pairs, `L_{u_1} = L_{u_2}` and `L_v = L_w`.

- (R5) Suppose also that `Gamma` is `K_{2,3}`-free. Then every vertex lies in
  at most two induced 4-cycles. If it lies in two, one is of centre type and
  the other is of axis type. Consequently, for `m, n >= 4`, neither the torus
  grid `C_m □ C_n` (Euler characteristic `1`), nor the hypercube `Q_4`, nor
  the Clebsch graph (Euler characteristic `3`) has a faithful reflection
  representation in `GL_3(R)`. Every vertex of those graphs lies in at least
  four squares.
- (R6) Suppose `Gamma` has girth at least 5 and minimum degree at least 2.
  Then all centres `[p_v]` are distinct and all axes `[L_v]` are distinct. The
  points and lines then form a configuration in which each line `[L_v]`
  carries the `deg v` points `[p_u]` with `u ~ v`. There may be further
  one-sided incidences.

So every square of `Gamma` is built from shared centres or shared axes, and
by (R1)–(R3) such sharing is very rigid. In particular, when `Gamma` has no
two vertices sharing a centre or an axis, `Gamma` has no induced 4-cycle and
`W` is word-hyperbolic.

**(C) Computation** (heuristic, not exhaustive). The runnable scripts are in
the artifacts and the numbers in `RESULTS.md`.

- Without (R1)–(R2), annealing over integral anti-flags with entries in
  `[-B, B]` finds triangle-free, `K_{2,3}`-free configurations of positive
  Euler characteristic:
  - `B = 1`: `4 chi = 5`, `V = 30`;
  - `B = 2`: `4 chi = 56`, `V = 153`.

  Every one is non-faithful. Exact kernel search finds relators of length
  three coming from the shared-centre transvection mechanism behind (R1)
  and (R2).
- With (R0)–(R3) imposed, no configuration with `chi > 0` was found by any of
  these searches:
  - annealing over all anti-flags, for `B <= 2`;
  - unions of at most two orbits of the signed-permutation group, for
    `B <= 3`;
  - unions of at most three orbits of an order-24 hexagonal group, for
    `B <= 2`.

  Here (R0) means (A3), triangle-free and `K_{2,3}`-free.
- Exhaustive search (`exact.py`) for the Robertson graph (the (4,5)-cage:
  19 vertices, 38 edges, girth 5, `chi = 1`) finds no realization satisfying
  (A2), (A3) and (R6) with entries in `[-B, B]` for `B <= 2`. The deepest
  partial assignment reaches 8 of the 19 vertices. The Robertson graph is
  not the smallest girth-5 graph with `chi > 0`: deleting two adjacent
  vertices leaves an induced subgraph with 17 vertices, 31 edges and
  `chi = 1/4`. The same exhaustive search on that subgraph (a strictly
  stronger test) also finds no realization for `B <= 2`; the deepest partial
  assignment reaches 9 of 17 vertices.

**ESTABLISHED 2026-09-17** (parts A and B) by
[[sl3z-racg-witnesses-are-antiflag-configurations-proof]]. Part C is a
computational record only.
