---
rg: 2
id: thompson-f-is-not-amenable
kind: claim
title: Thompson's group F is not amenable
root: true
distinct_from:
  thompson-f-is-amenable: that is the amenable answer to the same named problem; this is the non-amenable answer, which would make F a finitely presented non-amenable group without free subgroups.
---

**OPEN.** Richard Thompson's group `F` is not amenable.

*Marked `root` because it answers a named open problem.* A proof would give a
finitely presented, torsion-free, left-orderable non-amenable group with no free
subgroups (`thompson-f-has-no-free-subgroups`). Survey: V. Guba,
arXiv:2305.07113v4 (2023). The opposite root is `thompson-f-is-amenable`. Source
map: `research/artifacts/thompson-f-amenability-map-2026-09-12.md`.

## Attempts

- **Free subgroups.** Excluded by `thompson-f-has-no-free-subgroups`. A proof
  needs a mechanism other than a free subgroup: a paradoxical decomposition
  without free groups, a uniform isoperimetric inequality, or a non-Ore pair in
  `K[F]`. Dies: no such mechanism is known for `F`.
- **Spectral gaps from property (T).** Excluded: `F` lies in `V`, which has the
  Haagerup property (`thompson-v-has-haagerup-property`), so every Kazhdan
  subgroup of `F` is finite and no Kazhdan-type uniform gap is available. The
  Haagerup property does not obstruct non-amenability either, since free groups
  have it.
- **Numerical cogrowth.** Cogrowth sampling for the standard generators
  (Elder–Rechnitzer–Janse van Rensburg, *Random sampling of trivial words in
  finitely presented groups*, Exp. Math. 24 (2015), arXiv:1312.5722;
  Haagerup–Haagerup–Ramirez-Solano, Int. J. Algebra Comput. 25 (2015)) is
  reported to point toward non-amenability. Elder–Rogers, arXiv:1608.06703,
  "identify two potential sources of error" in that method (abstract). Dies:
  finite data cannot certify an asymptotic growth rate, and this graph has read
  none of the numerical values. That is now a theorem:
  `thompson-f-moment-data-cannot-certify-nonamenability` shows that finitely many
  exact closed-walk counts are always matched by a symmetric measure reaching
  `+-1`. So no finite cogrowth computation, however exact, proves `||P|| < 1`.
  Such data certify only lower bounds on `||P||`, via orthogonal-polynomial zeros
  (`experiments/thompson-f/cogrowth_exact.py`).
- **Non-Ore certificate.** By `thompson-f-amenable-iff-group-ring-is-ore`,
  non-amenability is equivalent to a pair `a, b` in `K[F]` with no nonzero common
  multiple. A finite search can propose candidate pairs, but ruling out every
  multiple needs a structural invariant. Dies: none is known. What is excluded:
  - `(1 - a, 1 - c)` for all `a, c ≠ 1` (`thompson-f-binomial-pairs-have-common-multiples`);
  - `(1 - x_0, b)` for every `b` (`thompson-f-one-minus-x0-is-ore-with-every-element`, Guba
    2022);
  - `(1 - h, b)` for every `b`, when `h` is conjugate to `x_0^{+-1}`, `x_1^{+-1}` or
    `(x_1 x_0^-1)^{+-1}`. That is Guba's Question 3.20, answered here
    (`thompson-f-one-minus-x1-is-ore-with-every-element`).
  - homogeneous degree-one pairs `P_(1,m)` for all `m`, and the degree-two case
    `P_(2,1)` (Guba's survey arXiv:2305.07113, Theorems 3.10, 3.11, 3.14);
  - three-equation systems `Q_3` in linear forms of `x_0, x_1, x_2` (survey Corollary
    3.13).

  - either side a unit times a product of twisted binomials `1 + lambda g`, with `g` any
    one-bump element of `F`, whatever its endpoint slopes
    (`thompson-f-one-bump-binomials-have-common-multiples`). The families and product
    statements are `thompson-f-rescaled-x0-binomials-have-common-multiples`, which first
    covered `x_0^{+-1}`, all `x_n^{+-1}`, `x_1 x_0^-1`, `x_2 x_1^-1` and their conjugates.
  - every system `Q_k` over `F_2`, and every `Q_k` over any field in which at most one
    form has all three coefficients nonzero
    (`thompson-f-rescaled-x0-binomials-have-common-multiples`, item 5).

  Open candidates: `Q_4` over fields `≠ F_2` with at least two full trinomial forms and the
  degree-two case `P_(2,2)`, both named in the survey, with both sides outside the one-bump
  product class; and twisted binomials `1 + lambda g` with `g` multi-bump, where property O
  itself is open. Map: `research/artifacts/thompson-f-certificate-shapes-2026-09-12.md`.
- **Evacuation schemes and bounded flows.** Non-amenability is equivalent to a flow on
  the Cayley graph with bounded values and inflow at least `epsilon` everywhere, or an
  evacuation scheme in which each edge is used at most `C` times. This is survey
  Propositions 1.3 and 2.3, and by Proposition 2.4 (König) it can be checked on finite
  fragments. Dies for `C = 1`: the Cheeger constant of `F` is below 1 for
  `{x_0, x_1, x_1 x_0^-1}` and for `{x_0, x_1, x_2}` (survey Theorems 2.5, 2.6, 2.8). For
  `{x_0, x_1}` capacity 2 dies too: a finite subgraph of density `> 3.5` forces capacity
  `>= 3` (`thompson-f-evacuation-schemes-need-capacity-three`). Open for `C >= 3` there.
- **Schreier graphs of natural F-sets.** A non-amenable Schreier graph of any `F`-set would
  prove non-amenability (`thompson-f-not-amenable-from-orbital-schreier-graph`). Dies for
  every orbit of points or of finite configurations of `(0,1)`, and for every `F/H` with `H`
  containing a rigid stabilizer of an end interval: long `x_0`-rays toward an end are almost
  invariant (`thompson-f-end-rigid-schreier-graphs-are-amenable`). A certificate of this shape
  must use a coset space `F/H` whose `H` contains no end-rigid stabilizer.
- **Measured orbit relation (Monod's mechanism).** Monod proves `H(A)` non-amenable through a
  non-amenable orbit relation (arXiv:1209.5229, Theorem 1.1). Dies for `F`: its orbit relation
  on `(0,1)` is the dyadic affine relation, hyperfinite for every quasi-invariant measure
  (`thompson-f-interval-orbit-relation-is-hyperfinite`, refuting
  `thompson-f-interval-orbit-relation-is-nonamenable`). Map of classes:
  `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md`.
- **C*-simplicity of T, and a local subgroup certificate.** Non-amenability of `F` is
  equivalent to C*-simplicity of `T` (`thompson-f-not-amenable-iff-thompson-t-cstar-simple`,
  Le Boudec–Matte Bon and Haagerup–Olesen; route `thompson-f-not-amenable-from-t-cstar-simple`).
  It is also equivalent to the existence of one C*-simple subgroup of `T` containing two
  nontrivial disjointly supported elements (`thompson-t-disjoint-pair-cstar-simple-subgroup-criterion`,
  route `thompson-f-not-amenable-from-cstar-simple-disjoint-pair`). The most concrete witness
  shape is a free product `A * B` with a disjoint pair in `A`. Classical ping-pong is
  impossible there (`free-product-disjoint-pair-no-support-separating-element`), and no
  construction is known. Map: `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md`.
- **Finite-state expansion flows on the positive monoid.** A certificate for doubling is a flow
  `w(s, y)` on `M`, with outflow `>= λ > 1` and inflow `<= 1`. Dies when `w` depends on the forest `y`
  only through a finite tree automaton profile and the number of trees
  (`thompson-f-finite-state-flows-cannot-prove-nonamenability`). The step where it
  fails: every finite automaton has an idempotent state measure, which makes a random forest
  split-stationary, and averaging then gives inflow `>=` outflow. A certificate must read invariants with
  no idempotent measure (sizes, depths, exact shapes); this is the gate where Moore's idempotent-mean
  route also died (arXiv:1807.05469). Also dies when the rule reads the total caret count as well, and
  for flows on all of `F` that depend arbitrarily on the negative part `q_g` of the normal form
  (`thompson-f-degree-aware-automaton-flows-cannot-certify`). There a pumped vine plus a fair coin
  spreads the leaf count, and splitting moves its law by `O(1/√N)`. Open: rules that read per-tree
  sizes, depths or exact shapes of the positive part.
- **Bounded cohomology with separable coefficients.** Amenability is equivalent to
  `H^n_b(G; E) = 0` for all dual modules `E`. Dies for separable `E`: by Monod, arXiv:2112.13741,
  `H^n_b(F; E) = 0` for all `n >= 1` and every separable dual `E`. The node
  `thompson-f-bounded-cohomology-witnesses-need-nonseparable` records three consequences.
  - Every witness cocycle generates a non-separable weak*-closed module.
  - `l^p`, `L^p`, separable Hilbert and trace-class coefficients all die.
  - `H^*_b(F; l^1_0(F/H))` is `R` in degree 1, the Johnson class, and `0` above.

  The step where it fails is ergodicity with separable coefficients for a co-amenable lamplighter in
  `F'`. The same vanishing holds for the non-amenable groups `H(A)`. What survives: modules like
  `l^∞(F/H)`, meaning a subgroup `H <= F` that is not boundedly acyclic and violates Monod's Corollary 6.
- **Cohomological, l2 and cost invariants.** These certificates are: `β_n^(2) > 0`; a free p.m.p. action
  of cost `> 1`; a nonzero `H_b^n(F,E)`; `F ∈ C_reg` or `D_reg`. All of them die at one invariant: the
  amenable normalish subgroup `T = ⊕_n ⟨x_0^n h_0 x_0^(-n)⟩`, generated by bumps accumulating at `0`
  (`thompson-f-has-an-amenable-normalish-tail-subgroup`). `T` starts the commensurating chain
  `T ⊂ ⟨T,x_0⟩ ⊂ F`.
  - `β_n^(2)(F) = 0` for all `n` (BKKO).
  - `F` has fixed price 1 (Gaboriau VI.24(3)).
  - `H_b^n(F,E) = 0` for all separable dual `E` (Monod, arXiv:2112.13741, Theorem 2).
  - `H_b^n(F,E) = 0` for every dual `E` with no nonzero vector fixed by a tail `T_(≥M)` (tail gate).

  Claim: `thompson-f-cohomology-certificates-cannot-prove-nonamenability`. Dies: every member except
  non-separable modules with tail-invariant vectors, which is Johnson's invariant-mean module. So what
  survives is the root itself. Calibration: the same vanishing holds for the non-amenable groups
  `F_2 × Z` and Monod's piecewise-projective groups, so none of it is evidence for amenability.
  (swarm-0917, obstruction-miner, cohomology-index.)
- **Subgroup-pair certificates: interior rigid stabilizers, Hecke pairs, tdlc hulls, graph actions
  (2026-09-17).** Certificates built from one subgroup `H` or one action: (S) a non-amenable `Sch(F/H)`;
  (C) a non-amenable Schlichting completion of a commensurated `H`, or any non-amenable totally
  disconnected locally compact group receiving `F` densely; (G) an action on a connected locally finite
  graph. Claim: `thompson-f-subgroup-pair-certificates-collapse`.
  - *Invariant:* rigid interval subgroups `F[a,b] ≅ F` with infinite simple commutants `F(a,b)`, whose
    conjugates exhaust `F′`.
  - *(S) dies at co-amenability:* every `H ⊇ F[a,b]`, for any interior interval, is co-amenable, because a
    limit of conjugates contains `F′` and Følner sets of the abelian limit graph transfer back
    (`thompson-f-rigid-stabilizer-schreier-graphs-are-amenable`). This upgrades the end-rigid kill above
    to every stabilizer of a non-dense set, of a measure with a gap in its support, and to every confined
    subgroup.
  - *(C) and (G) die at the completion or stabilizer step:* every commensurated subgroup is `1` or contains
    `F′` (`thompson-f-commensurated-subgroups-are-trivial-or-normal`, through a disjoint-support commutator
    `[f₁⁻¹h^(m₁)f₁h^(−m₁), f₂⁻¹h^(m₂)f₂h^(−m₂)] = [f₁⁻¹, f₂⁻¹]`). So a tdlc hull is `F` itself, abelian or
    compact-by-abelian, and a graph action is free or factors through `Z²`.
  - *Survivors (exact):* Schreier certificates over nowhere-rigid `H`, i.e. `H` containing no `F[a,b]`,
    equivalently whose conjugates never accumulate on a subgroup containing `F′`. These include `H = 1`,
    so the surviving class is equivalent to the root. Calibration: `BS(1,2)` and Thompson's `T` have
    commensurated non-normal subgroups, so the collapse uses both the simple commutants and torsion-freeness.
  (swarm-0917-w5-f-nonamenable, obstruction-miner, host-geometry.)
- **Private pivot orders (triangular doubling certificates) (2026-09-17).** A total order on `M` under
  which every `m` has two private points in `S m` makes `S` double and gives non-Ore pairs
  (`thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`). Such an order exists iff no layer
  `M_D` contains a *stubborn set*: a finite set in which every point has at most one successor whose
  predecessors in the set are only itself. The minimum of a stubborn set has at most one private point.
  - *Dies for `S_(3,5)` (`P_(2,2)`):* a 1092-point stubborn set in degree 7
    (`thompson-f-p22-monomials-admit-no-private-pivot-order`).
  - *Dies for every generator set `X_m = {x_0..x_m}`, by hand:* take the forests on `D + m + 2` leaves
    (`D >= m`) with no caret across a cut into two blocks of at most `D + 1` leaves. A product of `z` that
    joins two roots in the same block keeps every peel inside the set, and a single tree with `D + 2`
    leaves cannot fit in one block, so that product has at least two predecessors in the set. The one
    product that crosses the cut has `z` as its only predecessor in the set. At `D = m` this set is
    exactly the computed core (2, 8, 40, 221, 1288, 7752 points)
    (`thompson-f-generator-sets-admit-no-private-pivot-order`).
  - *Survivors:* non-triangular doubling certificates, such as 2-to-1 Hall matchings not induced by an
    order. Among the pivot orders themselves, only sets with no stubborn set in any layer survive, for
    example `{x_a x_b x_c : a <= 2, b <= 3, c <= 4}`, where none appears through `D = 10`. Degree-one sets
    with gaps have cores at `D = |J| − 1` (computed), but the block construction does not cover them.
  (c-pz0, obstruction-miner, host-geometry.)
- **Unaccepted claims.** arXiv:1408.2188 claims non-amenability, and Shavgulidze's
  papers claim amenability (critiqued in arXiv:1102.0747). Neither is an accepted
  result. They are recorded so that no lane cites them as theorems.
