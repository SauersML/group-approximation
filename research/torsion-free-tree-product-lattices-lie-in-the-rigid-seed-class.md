---
rg: 2
id: torsion-free-tree-product-lattices-lie-in-the-rigid-seed-class
kind: claim
title: Every torsion-free cocompact lattice on a product of locally finite trees carries a quantum-rigid seed SFT, coding a vertex or end in each tree, with free finite-subgroup action on the boundary; so the Burger–Mozes simple groups and Wise's non-residually-finite lattices lie in the class 𝒞, and all such seeds are capped at NP
requires:
  - tree-product-lattices-carry-rigid-topologically-free-sfts
  - locally-finite-tree-end-shifts-are-quantum-rigid-sfts
  - quantum-rigidity-passes-to-subshifts
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
distinct_from:
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that defines 𝒞 and closes it under free and direct products starting from finite groups and Z; this adds every torsion-free cocompact lattice on a product of trees, including simple and non-residually-finite ones, which no product or free product of those reaches.
  tree-product-lattices-carry-rigid-topologically-free-sfts: that codes ends only (a minimal topologically free boundary SFT); this adds sinks, so vertex tuples become an isolated free orbit, and uses block rules to keep one orbit.
  bs12-rigid-seed-is-its-normal-form: that is the rigid seed of BS(1,2), a locally finite splitting with infinite cyclic vertex groups; this is the proper cocompact case on several trees, where the seed is a vertex tuple.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary lane proof below; not reviewed; no priority
claimed).
- Seed SFTs (S1)–(S3) and the class `𝒞` are as in `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`
  (bh-g2-buildings, bf61de7d0), which is also synthesis v6's (SEED) object.
- Notation for trees, the rules (R1)–(R2) and quantum rigidity are as in
  `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`.

## Setting

- `T_1, …, T_k` (`k ≥ 1`) are locally finite leafless trees with more than two ends.
- `Γ ≤ Aut(T_1) × … × Aut(T_k)` is discrete, torsion-free, cocompact on `T_1 × … × T_k`, and acts
  without inversions. So `Γ` acts **freely** on vertex tuples, with finitely many orbits.
- **Representatives.** Fix representatives `t_1, …, t_N` of the orbits of full vertex tuples. For every
  nonempty proper `I ⊆ {1, …, k}`, fix representatives of the `Γ`-orbits on `∏_(i∈I) V(T_i)` (partial
  tuples). There are finitely many in all. Let `𝒱_i ⊆ V(T_i)` be the finite set of all `i`-th
  coordinates of these representatives.

## The SFT

The alphabet at a site records, for each `i` and `v ∈ 𝒱_i`, a letter in `E(v) ∪ {∗}`. The reading of
`x(g)_(i,v) = e` is "the out-edge at `gv` is `ge`", and `∗` means "`gv` is the sink of `T_i`".
- **(R1) Descent.**
  - `x(gk)_(i,v) = k^(-1) x(g)_(i,v)` for `k` in a finite generating set of `Stab_Γ(v)`. It is finitely
    generated: it acts properly and cocompactly on `∏_(j≠i) T_j`.
  - For `v, v' ∈ 𝒱_i` in one orbit, with a fixed `c` such that `v' = cv`:
    `x(g)_(i,v') = c · x(gc)_(i,v)`.
  - `k` and `c` act on `∗` trivially.
- **(R2) Edges.** Each edge of each `T_i` is chosen as out-edge by exactly one endpoint. A sink chooses
  none.
- **(R3) Blocks.** Forbid, at a single site, `x(1)_(i, p_i) = ∗` for all `i ∈ I`, whenever `p = (p_i)_(i∈I)`
  is a representative (full or partial) whose orbit is **not** the orbit of the `I`-projection of `t_1`.

`Y` is the SFT defined by (R1)–(R3), and `y_*` is the point with sinks at `t_1 = (t_1^1, …, t_1^k)`.

## Theorem

1. `(Y, y_*)` is a seed SFT: (S1) `y_*` is isolated, (S2) `Stab(y_*) = 1`, (S3) `Γ·y_*` is dense.
2. `Y` is `D`-quantum rigid over every field for all large `D`. So `Γ ∈ 𝒞`.
3. Finite subgroups act freely on `∂Y` (trivially, as `Γ` is torsion-free). This is (S5) of v6.
4. **Cap.** `Γ` is finitely presented and CAT(0), with quadratic Dehn function. So its word problem is
   in NP: a van Kampen diagram of quadratic area is a polynomial certificate.

## Instances

- `k = 1`: free groups acting freely on trees. This recovers the tree seed.
- `F_m × F_n`, and more generally reducible lattices.
- **Burger–Mozes lattices.** Torsion-free, finitely presented, **simple** cocompact lattices
  (Burger–Mozes, Publ. Math. IHÉS 92 (2000); recalled, not re-read). They are the first recorded infinite simple
  members of `𝒞`.
- **Wise's lattices.** Non-residually-finite complete square complexes (recalled).

## Proof

**Structure of points.** Fix one tree `T = T_i`. By (R1), each vertex `w` of `T` gets a well-defined
letter `o(w) ∈ E(w) ∪ {∗}`, as in §1 of `locally-finite-tree-end-shift-rigidity-proof`: every vertex is
`gv` for some `v ∈ 𝒱_i`, since `𝒱_i` meets every orbit.
- **At most one sink.** By (R2) every edge is oriented and out-degrees are at most 1. Suppose `u ≠ u'`
  are sinks. On the geodesic between them, the end edges point into `u` and into `u'`, so some interior
  vertex has two out-edges on the geodesic. That is a contradiction.
- **A sink determines everything.** Let `u` be a sink. Every `z ≠ u` points to its neighbour `z'`
  toward `u`, by induction on `d(z, u)`.
  - If `z' = u`, the edge `{z, u}` is not oriented by `u`, so by (R2) it is oriented by `z`.
  - Otherwise `z'` points toward `u` by induction, so not along `{z, z'}`, and again `z` must orient it.
- **No sink.** Without a sink, the point is an end (§1 of the route).
- **So** points of `Y` are tuples `(p_1, …, p_k)` with `p_i ∈ V(T_i) ⊔ ∂T_i`, subject to (R3). Vertices
  are isolated in each coordinate, and ends are the limits of vertices converging to them.

**(S1) and (S2).**
- The pattern "`∗` at every `(i, t_1^i)` at site 1" has cylinder `{y_*}`, by the paragraph above.
- `Stab(y_*) = Stab_Γ(t_1) = 1`, because the action on tuples is free.

**(S3).** Let `p ∈ Y`, and let `I` be its set of sink coordinates.
- **`I = {1, …, k}`.** Every full tuple is `g t_j` for a unique `g` and `j`. The site `g` sees `∗` in the
  whole `t_j`-block, so (R3) forces `j = 1`. Hence `p = g y_*`.
- **`I` proper, possibly empty.** By (R3), `p_I = g_0 t_1^I` for some `g_0` (vacuous if `I = ∅`).
  - `Γ_I := Stab_Γ(t_1^I)` acts properly and cocompactly on `∏_(i∉I) T_i`. Its orbits on vertex tuples
    correspond to the `Γ`-orbits of full tuples with `I`-part in `Γ t_1^I`, and there are finitely many.
  - So the orbit `Γ_I · (t_1^i)_(i∉I)` is `R_0`-dense in the max-metric, for some `R_0`.
  - Let `H_i^(n)` be half-trees shrinking to `g_0^(-1) p_i` (`i ∉ I`). Pick vertices `w_i^(n)` in
    `H_i^(n)` at distance more than `R_0` from its complement. Choose `s_n ∈ Γ_I` whose orbit point lies
    within `R_0` of `(w_i^(n))`.
  - Then `g_n = g_0 s_n` has `g_n t_1^i = p_i` for `i ∈ I`, and `g_n t_1^i → p_i` for `i ∉ I`. So
    `g_n y_* → p`.

**Rigidity.**
- **One tree with sinks.** The one-tree proof (§§2–4 of the route) goes through with sinks. Lemma 2
  holds because `k ∗ = ∗`. Lemma 3 is unchanged: "both" and "neither" orienting an edge are still
  forbidden. In the chain argument, `O_w(∗)` is one more side label, orthogonal to the forward and
  backward labels at `w`. Several base vertices per orbit cause no trouble: Lemma 1 turns each
  `c`-rule of (R1) into `O_(i,v')(g; e) = O_(i,v)(gc; c^(-1) e)`, so the descent to vertex idempotents
  is unchanged.
- **Several trees.** Coupling holds: `Stab_Γ(v)` has finitely many orbits on each vertex orbit of
  `T_j`, by cocompactness on the product. So item 1 of `tree-product-lattices-carry-rigid-topologically-free-sfts`
  makes the join of the `k` sink-end shifts (R1)+(R2) rigid.
- **Carving.** `Y` is cut out of that join by (R3), so it is rigid by
  `quantum-rigidity-passes-to-subshifts`.

**Cap.** `Γ` acts properly and cocompactly on the CAT(0) square complex `T_1 × … × T_k`, so it is
finitely presented with quadratic Dehn function (Bridson–Haefliger III.Γ; recalled). ∎

## What this says about CAP

- **Every tree-type seed is capped.**
  - Here, at NP.
  - For locally finite splittings, bh-g1-universal-point shows the tree layer is Britton's normal form
    (`bs12-rigid-seed-is-its-normal-form`, f6aedfd93), so it is complexity-neutral.
  - With `quantum-rigidity-passes-to-subshifts`, the carving and the deterministic layers are neutral too.
- **Where a cap could fail.** Only inside a vertex or relative seed that encodes computation (bh-free-56,
  bh-invent-03), or in a non-Brin–Thompson actor (bh-invent-11).
- **What this does show.** `𝒞` contains finitely presented simple groups outside every recorded
  finite-state Li coding. So "simple and in `𝒞`" is no obstruction, and the gate is purely about
  complexity.

## Lesson for general BH

A seed is a unique origin that local rules can recognize. On products of trees it is a vertex tuple,
rigid by coupling and carved to one orbit by block rules. So every torsion-free tree-product lattice,
simple ones included, satisfies the seed gate. The price is geometric: these seeds only see CAT(0)
geometry, and their word problems sit in NP. Beating CAP needs an origin whose recognition itself
costs computation. Trees and products never supply that.
