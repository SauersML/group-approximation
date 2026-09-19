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
  (`experiments/thompson-f/cogrowth_exact.py`). The best certified value on the 32 published terms
  (Elvey Price–Guttmann, arXiv:1706.07571) is `||P|| > 0.910677`
  (`thompson-f-norm-bound-from-epg-32-term-moments`). Exact extension past word length 62 and
  Dirichlet-eigenvalue test vectors on marked-forest window sets were both scouted there and do not
  beat it within reach.
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
  sizes, depths or exact shapes of the positive part, and flows on pairs of forests.
- **Flow rules reading an observation (the observation gate).** `thompson-f-flow-certificate-observation-gate`:
  a flow rule that reads only an observation `Ψ` of the forest exists iff `Ψ` has positive shadow defect
  `δ_λ(Ψ)`, by Sion's minimax theorem. So non-amenability is `δ_λ(id_M) > 0`, and every flow kill is a
  dominated shadow law. Dead observations: constants (Ore property), Schreier graphs with Følner sets,
  profile plus tree count, and now profile plus tree count plus total caret count (a random right-comb
  padding over the pumping period). *Invariant:* a dominated shadow law. Dies: every flow reading only
  coarse or finite-state data. Not covered: unbounded per-tree data and reduced pairs of forests.
  (swarm-0917, obstruction-miner.)
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
- **Invariant pivot orders.** A pivot-order certificate
  (`thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`) is killed when the order is
  left- or right-invariant on `F`, for every finite set
  (`thompson-f-invariant-pivot-orders-cannot-certify-doubling`). The step where it fails: two private
  points at `m` force a two-sided descent `g m ≺ m ≻ g^-1 m` with `g ∈ S^-1 S \ {1}`. Invariance turns
  this into `c ≺ 1` and `c^-1 ≺ 1`. The failure occurs at any deep `m`, where all competitors are
  positive, and deep elements exist by common right multiples.
  - An order that first compares a bi-ordered quotient only certifies one fiber of `S`, which must
    itself double and have at least four elements.
  - A surviving certificate needs a non-invariant order in which every deep `m` is a two-sided local
    maximum.
  - Computed: caret-count-first orders survive on sampled deep monoid elements but fail in group form.
- **Pivot orders: the tail splits off, and the staircase law (2026-09-18).** Two results on the
  pivot-order class, which is the certificate of
  `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`.
  - *Tail splitting* (`thompson-f-stubborn-sets-split-off-the-tail`, OPEN — demoted at landing on
    2026-09-18, see below). Writing `z ∈ M` as `(u ; v)` with `u` the first `K(S)` roots,
    `s z = (s̄ u ; v)` and **every** factorisation `w = s' z'` keeps the same tail `v`. So
    stubbornness is a fibrewise property of the finite prefix worlds
    `P_a = {forests with K roots and a carets}`, `|P_a| = f(K+a, K)`. Two consequences: a private
    pivot order exists iff `core(P_a) = ∅` for every `a`, a sequence of finite computations with no
    truncation parameter; and the published `letters <= L` windows were complete, so every "no core"
    row is a statement about the whole layer `M_a` (this removes the "computed only, inside
    `M_(D, m+D)`" caveat on the `X_m` layers below `D = m`). Two of three referee lenses refuted the
    third advertised consequence — that an empty core in all layers `<= A` certifies
    `|S Y| >= 2|Y|` "strictly stronger than `Λ_S(D) >= 2`". It is not stronger but *equivalent*:
    `thompson-f-monomial-doubling-ratio-is-a-finite-computation` defines `Λ_S(D)` as an infimum over
    every finite subset of the whole layer and proves the window lossless, so that corollary is a
    re-derivation of an established finite criterion, and it reaches strictly fewer layers than the
    exact `Λ` values do (`S_(3,5)`: `A = 6` versus `D <= 12`). The reduction itself (items 1, 2, 3,
    5) was checked line by line and reproduced by all three lenses, in three independent
    implementations; it is parked OPEN pending a referee pass on the corrected text.
  - *The search order does not matter, only the depth* (`thompson-f-staircase-sets-have-stubborn-layers`,
    OPEN). For the staircase sets `S(m,d) = X_m X_(m+1) ... X_(m+d-1)` the first stubborn layer obeys
    `2 a_min + 1 = 3^(d-1) (2m+1)` on all fourteen computed cases, with no failure: `a_min = m` for
    `d = 1`, `m = 1..6` (proved); 1, 4, 7, 10, **13** for `d = 2`, `m = 0..4`; 4 and **13** for
    `d = 3`, `m = 0, 1`; **13** for `d = 4`, `m = 0`. The three bold entries were predictions made
    before the layer was computed, and each required an empty core one layer below and a verified
    stubborn core at the layer itself — at `(4,2)` that is an empty core on 31 865 925 points and a
    7 470 184-point core on **121 580 760** points. *The invariant is the depth, not the order.*
    Consequence: the survivor recorded in the bullet above,
    `{x_a x_b x_c : a <= 2, b <= 3, c <= 4} = S(2,3)`, is predicted to have `a_min = 22`; the census
    now reaches `a = 12` (17 298 645 points) and is ten layers short, so its "survival" is an
    artefact of depth. Under the law no staircase set admits a private pivot order at all, and the
    class is dead on the whole Guba family. Also proved: a common left factor is invisible
    (`S = t S''` has the same cores as `S''`), so `a_min(S(0,d)) = a_min(S(1,d-1))`, checked at a
    33-million-point layer.
  - *And plausibly the class is dead outright* (`thompson-f-monomial-sets-all-have-stubborn-layers`,
    OPEN). An exhaustive census of the degree-2 monomial sets with letters `<= 3` finds **no** set
    with `|S| >= 2` and no stubborn layer. If that holds in general, the triangular doubling
    certificate has no instance anywhere in `F`, and any doubling proof must be non-triangular (a
    Hall 2-to-1 matching not induced by an order, or a flow). All 57 sets with letters `<= 2`, and
    all 165 sets of size 2 or 3 with letters `<= 3`, are resolved with `a_min <= 10`. A congruence
    shortcut is excluded: the divisibility in the staircase law fails for 26 of those 57 sets.
  - *Dead here:* need 176cdb5a, an order making every deep `m ∈ R(S_(3,5))` a two-sided local
    maximum, is vacuous as a route step: it is necessary for a pivot certificate of `P_(2,2)`,
    whose sufficient condition `thompson-f-p22-monomials-admit-no-private-pivot-order` already
    refutes. Also dead: bounded-size gadgets. The 24-point `S(1,2)` core is a *minimal* stubborn set
    (no one-point deletion and no subset of size `<= 4` is stubborn), and inside each of its six
    mirror-paired profile classes every point has five private successors out of `|S| = 5`. So a
    proof of the law needs a gadget whose size grows with the core (2, 24, 1092, 81224 along
    `d = 2`), not a fixed pattern.
  (e2-w2-f-pivot-order, swarm-0917, compute-scout, census-computation.)
- **Co-amenable non-amenable hosts (heretic, swarm-0917).** The routes above share three
  assumptions:
  1. the certificate lives on `F` itself;
  2. the witness uses `F`'s own dynamics;
  3. the witness is read from finitely supported data.

  Denying 1 and 2 gives a route: show that `F` is co-amenable in some non-amenable host `G`.
  Then any invariant mean on `F` would yield one on `G`.
  - A transfer lemma is established:
    `co-amenable-subgroups-transfer-hyperfinite-orbit-relations`. A co-amenable subgroup with
    a hyperfinite measured relation forces the host's relation to be hyperfinite. It needs no
    amenable stabilizers, unlike the Zimmer-action version, which is circular for `F`.
  - Consequence: `thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts`. `F` is not
    co-amenable in `T` or `V`, nor, by Eymard with `F`'s fixed-point measures, in circle hosts
    moving `0` or Cantor hosts moving `0^∞` and `1^∞` out of the pair. It is also not
    co-amenable in the Lodha–Moore group or in Monod's `H(A)` for `0 ∈ P_A`.
  - Dies: each host's non-amenability is witnessed on a space where `F` is amenable. On the
    boundary `F` has a fixed point, and on the line its Lebesgue orbit relation is hyperfinite.
    The co-amenability hypothesis carries that witness up to `G` and contradicts it.
  - A host route survives only with a witness for `G` whose restriction to `F` is already
    non-amenable, and that is a direct certificate for `F`.
  - Not covered: `nV`, the group `⟨t ↦ t + 1/2, b⟩`, and hosts certified by other witnesses.
  - Denial 3 is already recorded as `thompson-f-ore-obstructions-must-see-finite-support`.
- **Numerical cogrowth, exhausted at the published length (compute-scout, swarm-0917;
  refereed and demoted 2026-09-18).** The moment route on the 32 published Elvey
  Price-Guttmann terms is closed from both sides at odd truncation:
  `thompson-f-32-term-cogrowth-bound-is-the-moment-optimum`, which is **OPEN**, not
  established — referee lenses 2 and 3 refuted it. The headline below (`N = 31`, odd) was
  reproduced independently by all three lenses and is not in doubt; what is open is the
  even-`N` half of the table, now
  `even-degree-localizing-hankel-attains-truncated-moment-optimum`.
  - *Invariant:* the largest eigenvalue of the 16×16 truncated multiplication operator `J` on
    `R[x]_{≤15}` with `<p,q> = L(pq)`, `L(x^j) = c_j/16^j`. Its spectral measure at the
    constant `1` is a 16-atom measure with **exactly** the 32 published moments, so every
    certificate whose only input is "a positive measure with these moments" dies at it. The
    certified value `||P|| > 0.910677539452` and the ceiling `0.910677539453` agree to 13
    digits.
  - `theta*(N)` is tabulated for all `N ≤ 31` — the exact optimum at odd `N`, a certified
    lower bound at even `N` (optimality there is the open prerequisite). The deficit falls
    like `N^{-0.61}`, fitted on the odd rows `N = 15, 23, 31`, so certifying `||P|| > 0.92`
    needs about 42 exact terms, `> 0.95` about 263, against the 32 that exist. With
    `thompson-f-moment-data-cannot-certify-nonamenability` (no finite data proves `||P|| < 1`)
    the cogrowth route is now bracketed on both sides.
  - *The competing class is priced.* A finite window `A` gives `lambda_max(A_A)/4 ≤ ||P||`,
    which is the matrix-moment (NPA) relaxation. On the 4-regular tree the window at radius
    `r` and the moments at word length `2r` agree to `10^-13` at `r = 4, 6, 8, 10, 12`
    (measured; the offered reason — the Perron vector of a tree ball is radial and the
    radial subspace is the Krylov space of `delta_e` — is proved only at odd truncation and
    every checked radius is even, so this is a measurement, not a theorem).
    In `F` the window wins by only `+0.00022` per unit radius (measured to `r = 12`,
    `|B_12| = 676061`, bound `0.870273`), while `|B_r|` multiplies by `2.76`: extrapolating
    both, matching the existing `0.9107` needs radius `≈ 27`, about `3×10^12` vertices —
    an extrapolation, not a measurement.
  - *Isoperimetric certificates die on direction.* Minimising `|dA|/|A|` over subsets of `B_11`
    (max-density subgraph, exact counts) gives `|A| = 41136`, `|dA|/|A| = 1.40743`, hence
    `h(F, {x_0,x_1}) ≤ 1.40743`; but Kesten-Dodziuk `h ≤ 4 sqrt(1-||P||^2)` converts a *lower*
    bound on `h` into an upper bound on `||P||`, so an explicit set yields only
    `||P|| ≥ 1 - |dA|/(4|A|) = 0.6481`, the indicator Rayleigh quotient.
  - *What survives:* a certificate that reads the group beyond the numbers `c_n` — off-diagonal
    counts `w_n(g)`, or a window in a graph that converges at the same rate per radius but is
    exponentially smaller. The concrete candidate is a Schreier graph `Sch(F/H, S)` for an
    **amenable** `H ≤ F` (say `H = <x_0, h> ≅ Z wr Z` for a one-bump `h` whose `x_0`-translates
    are disjoint): the Cayley graph covers it, so `||P_{Sch}|| ≥ ||P||`, and for amenable `H`
    the quasi-regular representation is weakly contained in the regular one, so
    `||P_{Sch}|| = ||P||` and windows in `Sch` certify `||P||` itself. Measured here:
    `|H ∩ B_r| = 1, 3, 5, 7, 9, 11, 15, 25, 43, 69, 105, 155` for `r ≤ 11`, growth `1.48`
    against `2.774` for `|B_r|`. **The saving is unmeasured in both directions** (corrected
    2026-09-18, referee lens 3; the earlier "about `1.85` per radius, about `10^7` vertices"
    was wrong). `|Hg ∩ B_r| ≤ |H ∩ B_{2r}|` gives `|Sch_r| ≥ |B_r| / |H ∩ B_{2r}|`, a
    *lower* bound on the Schreier ball, worth at best `2.76/1.48^2 = 1.26` per radius at the
    measured rates; the computed coset count is an upper bound whose own ratios run `2.7-3.0`.
    Honest bracket at radius `27`: `10^3` to `10^12` vertices. Blockers, both exact: a
    canonical form for the cosets `Hg` — a decidable normal form for `Z wr Z` inside `F` — so
    that one can BFS directly in `F/H`; and the growth rate of the Schreier ball itself,
    which is what would decide whether this is an accelerator at all. Nobody has done either.
- **Crossing the observation gate: the exact tail is inert above an idempotent prefix reading
  (2026-09-17; refereed, and the first framing of it was refuted on scope).** Working inside the gate's
  own definitions, `thompson-f-exact-tail-observations-have-zero-defect` computes the shadow defect of
  an observation that is *not* coarse. Fix finite `S ⊆ M`, let `I` be its largest generator index,
  `D = max deg s`, `K = I + D + 1` (so `K = m + 2d` for `S = S_(m+1,m+d+1)`), let `(Q, δ, ℓ)` be a tree
  invariant whose reachable states carry an **idempotent** probability, and let
  `Ξ(y) = ((q(t_0), ..., q(t_(K−1))), (t_K, t_(K+1), ...))`: the `Q`-states of the first `K` trees, and
  the **exact shapes** of every later tree. Then `δ_1(Ξ) = 0`, and also with the germ datum at the
  endpoint `0` (the leftmost-leaf depth of `t_0`) adjoined. *Where it dies:* the splits of `S` touch only
  the first `I + 1` trees and create `I + d + 1`, so for a forest of i.i.d. idempotent towers the coupling
  of `split_s Y` at `N = n` with `Y` at `N = n + d` is an **exact identity** on the tail and on the
  prefix state vector, and the whole cost is the `d/(L − n_0 + 1)` of mixing over the tree count.
  - *What it closes.* The part of the gate's Scope marked open ("observations reading unbounded data of
    individual trees (sizes, depths, shapes)") for every tree outside a bounded window, **provided** the
    bounded window is read through an idempotent-carrying invariant: sizes, depths, spines, exact subtree
    structure and every unbounded invariant of all but `K` trees contribute nothing on top of such a
    prefix reading.
  - *What it does **not** close, and the referee's reason for refuting the node's first framing
    (event `31e58aeb`).* It does **not** follow that a certificate must read the exact shapes of the
    first `K` trees. Idempotency is load-bearing, and prefix **depth** and prefix **size** carry no
    idempotent probability — for depth, `F(k) = P(depth <= k)` would satisfy `F(k) = F(k−1)^2`, forcing
    `F ≡ 0` or `F ≡ 1`. So `Ψ(y) = ((depth t_0, ..., depth t_(K−1)), (t_K, t_(K+1), ...))` is a
    coarsening of no such `Ξ`, reads no exact prefix shape, and is untouched. The residue is therefore
    not `π_K` alone but the whole interval between idempotent-carrying prefix observations and `id_M` —
    every (non-idempotent prefix invariant, exact tail) pair, of which `(Ξ, |y|)` is one member.
  - *Sharpness:* blurring only the first `K − 1` trees leaves total variation `15/16` for `S_(2,3)`,
    `s = x_1` (exact arithmetic) — a statement about this model family, not a lower bound on `δ`.
  - *Residue, partly recorded as `thompson-f-prefix-observation-shadow-defect`:* (1) is `δ_λ(π_K) > 0`
    for the prefix observation `π_K(y) = (t_0, ..., t_(K−1))`? — a yes proves this root; (2) does
    `δ_1(π_K) = 0` transfer back to `δ_1(id_M) = 0`? — a yes with (1) no proves
    `thompson-f-is-amenable`. Also open: `(Ξ, |y|)` and, more generally, every prefix invariant with no
    idempotent state measure paired with the exact tail.
  - Script and exact numbers (reproduced byte-identically by all three referees):
    `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py`,
    `experiments/thompson-f-shadow-defect-2026-09-17/output.txt`.
  (swarm-0917, e2-w2-f-shadow-defect, inverter, probability-random.)
- **Co-amenable hosts: every circle embedding, and line hosts with non-integral end germs
  (swarm-0917-w9-z-pull).** This extends the heretic's bullet to two whole classes of hosts.
  - *Circle hosts, any embedding.* Established as
    `thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts`, via the imported
    `margulis-circle-weak-tits-alternative`.
    - Every `F`-subgroup preserves a probability on `S^1` (Margulis), and Eymard lifts it to
      any host in which `F` is co-amenable.
    - The host's rotation homomorphism then kills every minimal circle host, including `T`
      under every embedding `F ↪ T`, whatever witnesses the host's non-amenability, free
      subgroups included. Minimal circle hosts would force a finite-index abelian subgroup
      of `F`.
    - The remaining circle hosts reduce to a line host `Q ≤ Homeo_+(R)` containing `F'`
      co-amenably in an arbitrary embedding, or to a gap host over a Cantor support.
    - Invariant: the Margulis measure. Dies at: Eymard's transfer.
  - *Line hosts with non-integral end germs.* Established as
    `thompson-f-co-amenable-hosts-have-integral-end-germs`.
    - Let `G ≤ Homeo(R)` preserve null sets, contain Thurston's `F`, and have one element
      that is affine but not an integer translation near `+∞` or `−∞`. Then no subgroup of
      `F` is co-amenable in `G`.
    - Mechanism:
      - Farey germs show that `F` realizes all of `PSL_2(Z)` off `Q`;
      - `a` drags the end germ `s` to a global map;
      - a Shimizu iteration makes `⟨PSL_2(Z), s⟩` dense;
      - Carrière–Ghys and the transfer lemma finish the proof, with a countable reduction for
        uncountable hosts.
    - This covers `⟨t + 1/2, b⟩`, left open above, and makes Lodha–Moore l.136–138 rigorous.
      It also covers `⟨F, 2t⟩`, Monod's `H`, and `H(A)` for every `A ≠ Z` containing `F`.
    - Inside `H`: a co-amenable host of `F` has only integer-translation germs at `±∞`.
    - Invariant: the end-germ homomorphisms `∂_±`. Dies at: density of
      `⟨PSL_2(Z), ∂_±g⟩`.
  - *Surviving host classes.*
    - Line hosts in which `F'` sits by a non-Thurston embedding.
    - Subgroups of `H` whose non-`PSL_2(Z)` pieces are all interior. The method only
      realizes `λγ` with `γx ∈ I` there, not `λ`; `G_0` is killed separately by explicit
      words.
    - Gap hosts, where co-amenability of `H ∩ K` does not descend to `K` (Monod–Popa).
    - Cantor hosts such as `nV`.
- **Schreier windows over `Z ≀ Z` for the norm lower bound (swarm-0917-w12-w12-f-follow,
  census-computation).**
  - *Setup.* `H = ⟨x_0, h⟩ ≅ Z ≀ Z` is amenable, so windows in `Sch(H\F)` give lower bounds on `‖P_F‖`
    that dominate those of Cayley balls.
  - *Answers need 6a72890d.* `H` is exactly the stabilizer of the tiling by `x_0`-translates of `[1/2,3/4]`
    decorated with standard bumps. Each coset has a unique computable representative
    (`thompson-f-z-wr-z-cosets-have-a-canonical-form`).
  - *Price, measured.* Schreier balls grow about `2.63` per radius, not the `1.85` behind the need.
    Radius 27 would be about `10^11` cosets.
  - *Per vertex the quotient wins, but not enough within reach.*
    - Schreier `B_11` gives `0.8846` on 77823 cosets, against `0.8648` for Cayley `B_11`.
    - Greedy Perron windows give `0.8966` at `4·10^5` vertices, gaining `0.004` per e-fold.
    - Beating `0.910677` needs about `10^7`–`5·10^7` vertices. It also requires `‖P_{H\F}‖ > 0.910677`,
    which is unknown.
  - *Status.* Not closed. It could not prove `‖P‖ < 1` in any case, since this is a lower-bound method.
- **Unaccepted claims.** arXiv:1408.2188 claims non-amenability, and Shavgulidze's
  papers claim amenability (critiqued in arXiv:1102.0747). Neither is an accepted
  result. They are recorded so that no lane cites them as theorems.
