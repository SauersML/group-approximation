---
rg: 2
id: fpbs-morse-deficit-vanishes-for-full-presentations
kind: claim
title: Well-founded Morse matchings over short trivial words almost exhaust the cycle dimension of every Bernoulli Cayley graphing
artifacts:
  - research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md
  - research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md
distinct_from:
  fpbs-bernoulli-cycle-tail-compactness: that asks for compact near-minimizing sequences among arbitrary graphings; this restricts to subgraphings of one Cayley graphing organised by cell matchings, so it additionally contains subgraphing attainment (Q3 of the artifact) and can fail even if the cost-Betti equality holds
  fpbs-bernoulli-morse-collapse-criterion: that proves the criterion and the limit formula; this is the open assertion that the limit is zero
---

**OPEN.** For every infinite group `Gamma` with a finite generating set `S`,

```text
lim_{L -> infinity} m(P_L) = 0.
```

Here `m(P_L)` is the Morse deficit of the list of all words of length at most `L` that are trivial in `Gamma`, as
defined in `fpbs-bernoulli-morse-collapse-criterion`.

By Theorem B there, this is equivalent to `C_sub(S) = 1 + beta_1^(2)(Gamma)`: the Bernoulli cost excess over the
Betti number is approached by generating Borel subgraphings of the Cayley graphing `Phi_S`.

**Stronger forms.**

- Deficit zero for one finite presentation. This is (Q1) of the artifact, and follows from this claim together with
  depth compactness (Q2).

**Instances that hold.**

- `Z^2`, and products of groups whose factors have generators of infinite order.

**Instances that are open and fixed-price-relevant.**

- Infinite one-relator groups. Here the target mass is exactly the proper-power ceiling `1/m`.
- Infinite Kazhdan groups.

A counterexample would need a group whose Bernoulli cost excess is not reached inside a Cayley graphing, or one where
the cost–Betti equality fails.

## Attempts

**Route a near-optimal graphing through the Cayley graphing (Q3).** Take a near-minimizing graphing `Psi`, write each
`Psi`-edge as a Cayley path of length `l`, and keep only the Cayley edges used. The attempt dies at the cost count:
the union of the paths can cost up to `l` times `c(Psi)`, and nothing forces the paths to share edges.

**Commuting-direction chains, as in the product calibration.** Each removed `s`-edge is recovered along the orbit of
a generator `c` of infinite order, through a commutator relator `[s, c]`. This needs every generator to commute with
an element of infinite order, independent of the generator itself. The attempt dies for torsion-free hyperbolic groups,
including hyperbolic one-relator groups and hyperbolic Kazhdan groups. There centralizers are cyclic, so a commutator
`[s, c]` with `c` of infinite order forces `c` to be a power of the root of `s`. The `c`-orbit chain then runs along
the `s`-line itself, and the recovered edge reappears among its own descendants.

**2026-09-17 (swarm-0917-w5-fp-cycle-tail): prove the limit through one finite list (Q1 or Q2).** This dies at an l2
mass bound. `fpbs-morse-mass-bounded-by-relator-boundary-rank` proves `mu(M) <= rho(R) = dim cl im d2^R` for every
finite list, so `m(R) = gap(R) + A(R)` with the relation gap `gap(R) = z - rho(R)`. The gap is not always zero:
`fpbs-lamplighter-fixed-list-morse-attainment-fails` shows `gap(R) >= 2^-(K(R)+1)` for every finite list on
`Z/2 wr Z`, while this claim holds there (`C_sub = 1`). So no fixed finite list can witness the limit in general. What
survives: `gap(P_L) -> 0`, so this claim is equivalent to `lim_L A(P_L) = 0`, asymptotic attainment of the l2 rank by
well-founded matchings. For finite presentations `gap = 0`, and there (Q1) is exactly `A(R) = 0`. Artifact:
`research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md`.

**2026-09-17 (swarm-0917-w5-pull-fp-1): dual-forest matchings along a two-incidence edge class.** This proves (Q1),
and hence this claim, fixed price and `C(b) = 1 + beta_1`, for every infinite `<S | w^m>` in which some generator is
used exactly twice in `w`. See `fpbs-one-relator-twice-used-letter-fixed-price`.

- By Weinbaum the boundary cycles are embedded, so each `s`-edge lies on exactly two distinct cycles.
- The dual graph on cycles has component `<w,t><w>`. The Freiheitssatz gives an element of infinite order in
  `<w,t>`, so the components are infinite.
- Matching each cycle to the `s`-edge toward its parent in a BFS forest around sparse iid markers gives mass
  `(1 - eps)/m`. Mass transport makes the trees finite, and children of a matched edge are exactly its tree children.
- This reaches the proper-power ceiling `1/m` with the single relator `w^m`.

It does not reach the general claim, and dies as a general method at the incidence count. If every letter is used at
least three times, an `s`-edge has `k >= 3` incidences. A matched edge is then a child of the matched edges of all
`k - 1` other incident cells, so well-foundedness needs a Borel peeling of the incidence hypergraph, which nothing
here supplies. Kazhdan groups, and one-relator groups in which every letter repeats, are untouched. Artifact:
`research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md`.

**2026-09-17 (swarm-0917-w5-pull-fp-3, transplanter, group-rings): split the premise, and fix the Q3 route by
letting S grow.** The Q3 attempt above dies because it keeps the long edges as Cayley paths. Keep them as generators
instead:

- Split each piece of a near-optimal `Psi` into translations `x -> gamma.x`.
- Truncate to finitely many labels `F`.
- Back up the `S_0`-edges that are not yet connected. They have vanishing measure by dominated convergence.

This gives `C(a) = lim_R C_sub^a(B_R) = inf_S C_sub^a(S)` for every free action. So
`lim_R lim_L m_(B_R)(P_L) = C(b) - 1 - beta_1`, and at a fixed `S` this claim is exactly
`C(b) = 1 + beta_1` plus `(Q3)(S)`, where `(Q3)(S)` is upward closed in `S`.

Consequences:

- The Morse form of the cost–Betti target is lossless once `S` may grow.
- The only surplus of this claim over the target is attainment at small `S`, which no route to tail compactness needs.
- A failure at one `S` does not refute the target.

Group-rings transplant: `rho` is the von Neumann rank of `d2` over `Z Gamma`, so it does not depend on the action. All
action dependence sits in `A`. Ring tools produce division-closure pivots, not `±1` acyclic Morse pivots, since
`[[1,1],[1,-1]]` has rank 2 and no admissible pivot pair. So they stop at `A`.

Still open here: `(Q3)(S)` at small `S` for nonamenable, non-treeable groups. Test cases are `<S | w^m>` and
2-generator Kazhdan groups. Claim `fpbs-cost-is-limit-of-cayley-subgraphing-costs`; artifact
`research/artifacts/fpbs/docs/adapted-generating-sets-make-morse-deficit-lossless.md`.

### 2026-09-17 (swarm-0917-w5-fp-morse, inverter, reframing): fixed-S price split; claim stays OPEN

**Result.** New ESTABLISHED claim `fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost`.

- **(H1)** `C_sub^a(S)` is antitone under weak containment at a fixed `S`. Approximate by conjugates and back up the
  generator edges that are not connected.
- **(H2)** `c_inv(S) = C_sub^(a_inf)(S)`.
- **(H3)** The hole at `S` holds iff `C_sub^b(S) = 1 + beta_1`, iff (P1) and (P2) hold:
  - (P1) `S`-fixed price;
  - (P2) the invariant Cayley cost is `1 + beta_1`.
- **(H4)** (P2) holds for Kazhdan and for amenable groups. So for Kazhdan groups the hole at `S` is exactly `S`-fixed
  price.

**Literature.** `fpbs-invariant-cayley-cost-literature-status` imports two sources.
- The hole at one `S` implies that the invariant cost of `Cay(Gamma, S)` equals `cost(Gamma)`. Beringer–Pete–Timár
  (arXiv:1609.07043) record that statement as unknown in general. This updates "We know no reference either way" in
  the collapse-criterion artifact.
- Hutchcroft–Pete give the invariant half at every `S` for Kazhdan groups, and they say their method cannot reach
  `cost*`.

**Biography of a counterexample.** A failure at `(Gamma, S)` is visible only at the factor-of-iid end: every free
action is at least as good at `S`. It comes through one of two channels:
- (P2) fails, which gives a Beringer–Pete–Timár counterexample;
- (P1) fails, meaning cost is attained invariantly inside `Cay(Gamma, S)` but not as a factor of iid.

**Dead ends recorded** in `research/artifacts/fpbs-fixed-s-price-split-2026-09-17.md`, Section 5:
1. **Percolation-cluster certificates.**
   - Unique cluster plus arrows gives `C_sub^b(S) <= 1 + theta_S(p)(d/2 - 1)`.
   - Not necessary: for `F_2` at `{a, b, ab}`, `p_u = 1` and the certificate gives 3, but the hole holds via the
     basis treeing.
   - For `beta_1 = 0` it needs `p_c = p_u` at `S`.
2. **Hyperfinite coarsening.** Relative cost over hyperfinite `H` fails because `S`-edges cross `H`-classes with density
   bounded below by the spectral gap (sketch). This is the same obstruction as Voronoi-cell contraction and as sliding
   bridges to crossing edges, where simultaneous replacements interfere.
3. **Stepwise Hutchcroft–Pete transfer.** Already dead by `fpbs-hp-condensation-bernoulli-exit` (A)–(B).
4. **FUSF of the Cayley graph.** On nonamenable groups with `beta_1 = 0`, FUSF = WUSF has infinitely many trees.

**Next falsifiable step.** Decide (P1) at a 2-generator Kazhdan `Cay(Gamma, S)`. A sufficient input would be this: does the
Hutchcroft–Pete invariant sparse subgraph, joined with iid, lie in the weak closure of factor-of-iid subgraphings of
`Cay(Gamma, S)`?

**2026-09-18 (swarm-0917-w6-w6-fp-pull, transplanter, operator-algebras): move Poulin–Wróbel's cutting
(arXiv:2606.23506, Theorem 3.4) to Bernoulli by replacing its `Z/n` phase windows with a Borel rule.** The attempt
dies for the whole fixed-position class whenever `Lambda = <P>` is nonamenable. New ESTABLISHED claim:
`fpbs-fixed-position-morse-matchings-die-on-bernoulli`.

1. **Heights force invariance.** Take a well-founded matching of each cell to its `s`-edge at one designated
   position. Its height sublevel sets `X_k` grow by at most `delta = mu(X \ A)` per level and are `2 delta`-almost
   invariant under every `p in P`.
2. **Bernoulli has a gap.** On Bernoulli, `L^2_0` restricted to `Lambda` is a sum of `l^2(Lambda / K)` with `K`
   finite. So the Kesten gap applies, and it gives `delta >= min(1/4, 3(1 - rho)/32)`.
3. **What it means.** Lemma 3.3's phases are not a removable artifact of the proof. Any cutting at a fixed position
   must build a structure that is almost invariant under `Lambda`.

**Survivors:**
- matchings whose position varies from cell to cell (dual-forest type);
- for `m >= 2`, schemes where the transversal is modulated;
- longer trivial words.

**Calibration:**
- `<P>` cyclic (twice-used letter, `m = 1`): no obstruction.
- PW's coset action: no gap, so no obstruction.
- The class already fails at a presentation of `F_3`.

Artifact: `research/artifacts/fpbs/docs/fixed-position-cutting-spectral-obstruction.md`.

**2026-09-18 (swarm-0917-w7-w7-fp-pull, transplanter, logic-computability): read Morse height as a coarse modulus
and ask whether bounded-height certificates can reach the ceiling.** This dies, for every nonamenable group, at the
routing tail inequality.

- *Dictionary.* A removed edge of recovery height `H` over relators of length at most `k` has its endpoints joined in
  `Phi'` by a path of length at most `(k-1)^H`. So a bounded-height matching retains a coarsely equivalent subgraphing,
  which is the Morse form of the CGdlS coarse modulus.
- *Where it dies.* `fpbs-quantitative-routing-tail-bound` then gives
  `2 nu(E_M^{>H}) >= h - d (|S| - 1 - mu(M)) |B_G((k-1)^H)|` on every free action.
- *Consequences when `beta_1 = 0`, which includes Kazhdan groups:*
  - bounded-height matchings have deficit at least `h / (d |B_G((k-1)^H)|)`;
  - near-optimal families over a fixed list keep mass `h/2` above every fixed height;
  - depth-one witnesses over `P_L` need `L >= log_d(h / (d eta))`.
- *What is ruled out.* Finite certificates of fixed `(k, H)` cannot succeed, and any proof of this node must build
  matchings with non-tight heights.
- *What is not ruled out.* This is not an obstruction to the node itself. `F_2 x Z` meets the inequality through
  geometric-stopping heights.
- *Status.* The node stays OPEN.

Claim: `fpbs-near-optimal-morse-matchings-have-non-tight-heights` (ESTABLISHED, written deduction).

### 2026-09-18 — swarm-0917-w8-w8-fp-pull (transplanter, stability-approximation): single-letter variable-position matchings die on Bernoulli

- *Approach.* Extend the dual-forest matching of `fpbs-one-relator-twice-used-letter-fixed-price` to a letter `s`
  used `k >= 3` times, by any Borel peeling of the incidence hypergraph (a variable position in each cell).
- *Result (negative, ESTABLISHED).* `fpbs-single-letter-morse-matchings-die-on-bernoulli`. Every such matching on
  Bernoulli has deficit `>= (k - 1)(1 - rho)/(6 k^2)`, where `rho` is the Kesten radius of the transport group
  `Lambda_s = <h_a h_b^{-1}>`.
- *Where it dies.* (M3). Height sublevels are `2k delta`-almost `Lambda_s`-invariant, the gap forces one thick level,
  and the top property bounds that level's mass by the unmatched mass.
- *Changes belief.* `abaBabcdcDcd` has all four `Lambda_s` nonamenable, yet the group (`F_2 *_Z F_2`) has fixed price.
  So one-relator single-letter routes are closed even where the node holds.
- *Not ruled out.*
  - Multi-letter matchings.
  - `m >= 2` cell types.
  - Growing word lists `P_L`. This is where the node lives.
- *Status.* The node stays OPEN.
