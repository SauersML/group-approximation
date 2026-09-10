---
rg: 2
id: fpbs-benjamini-schramm-universal
kind: claim
title: Every nonamenable locally finite Cayley graph has a Bernoulli bond nonuniqueness interval
root: true
goal: true
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/creative-branches.md
  - research/artifacts/fpbs/exploration.md
  - research/artifacts/fpbs/spectral-spike.md
  - research/artifacts/fpbs/exploration-pivotal-projections.md
---

**UNIVERSAL GOAL; OPEN.** For every nonamenable finitely generated group
`Gamma` and every finite symmetric generating set `S` not containing the
identity,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)),
```

where `p_c` is the threshold for the appearance of an infinite cluster and
`p_u` the threshold above which the infinite cluster is unique, for
independent Bernoulli **bond** percolation. Equivalently, by
Benjamini--Lyons--Peres--Schramm (1999), there is a single parameter at which
infinitely many infinite clusters appear almost surely. The
every-generating-set quantifier is essential: Pak and Smirnova-Nagnibeda
(2000) already produce *some* Cayley graph with a nonuniqueness phase for
every nonamenable group, and Section 6 of the priority assessment names the
passage from one convenient generating set to all of them as a real part of
the difficulty.

**What is known unconditionally.**

* *Hyperbolic and nonunimodular geometries.* Hutchcroft, *Percolation on
  hyperbolic graphs*, arXiv:1804.10191, proves `p_c<p_u` on every nonamenable
  Gromov-hyperbolic quasi-transitive graph; Hutchcroft,
  arXiv:1711.02590, proves `p_c<p_h<=p_u` whenever the automorphism group has
  a nonunimodular quasi-transitive subgroup, which covers `T_k x Z^d`.
  Recorded jointly as `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`.
* *Acylindrically hyperbolic groups.* Choi--Seo, arXiv:2508.08932, prove a
  nonuniqueness phase on **every** Cayley graph of an acylindrically
  hyperbolic group, so relatively hyperbolic groups, mapping class groups and
  rank-one CAT(0) groups satisfy the full quantifier. Recorded as
  `fpbs-sc-choi-seo`.
* *The L2 criterion.* Hutchcroft, *The L2 boundedness condition in nonamenable
  percolation*, arXiv:1904.05804, states that boundedness of the critical
  connectivity matrix `T_{p_c}(u,v)=P_{p_c}(u <-> v)` as an operator on
  `l2(V)` implies this conjecture. That implication is
  `fpbs-critical-l2-implies-nonuniqueness`, imported by
  `fpbs-critical-l2-criterion-reference`. The hypothesis is Hutchcroft's own
  conjecture, strictly stronger than the present goal, and is recorded here as
  `fpbs-nonamenability-bounds-critical-connectivity-operator`.
* *The cost route.* Lyons, arXiv:1109.5418, Section 1: a finitely generated
  group that does not have fixed price with cost one has a nonuniqueness phase
  on every one of its Cayley graphs
  (`fpbs-non-fixed-price-one-has-nonuniqueness`). Lyons writes the proof for
  **site** percolation and remarks that essentially the same proof applies to
  bond percolation; that remark, not a separate written proof, is what carries
  the theorem into the bond statement above. Consequently the only case this
  route leaves is `fpbs-fixed-price-one-percolation-kernel`, nonamenable
  groups of fixed price one, and a counterexample to this goal would have to
  come from that class.

**Decomposition supplied by the 2026-09-08/09 archive.** Seven live routes
target this claim; every one of them is conditional on an OPEN estimate, and
none asserts more. Two further routes are recorded and dead:
`fpbs-dead-inverse-laplacian-expansion`, killed by
`fpbs-inverse-connectivity-matrix-not-laplacian` (the four-cycle gives a
positive off-diagonal entry of the inverse), and
`fpbs-dead-uniform-tight-routes-contradiction`, killed by
`fpbs-cost-one-routes-cannot-be-uniformly-tight` and
`fpbs-quantitative-routing-tail-bound`.

* `fpbs-benjamini-schramm-two-cost-cases` splits on whether the group has
  fixed price one: the negative case is closed by Lyons, the positive case is
  the open kernel `fpbs-fixed-price-one-percolation-kernel`.
* `fpbs-universal-pivotal-route` asks for the uniform near-critical linear
  pivotal budget `fpbs-pivotal-budget-universal` and combines it with the
  proved conditional implication `fpbs-pivotal-budget-implies-nonuniqueness`.
* `fpbs-universal-integrated-pivotal-route` weakens that to
  `fpbs-pivotal-nonconcentration-universal`, which forbids the sensitivity
  mass `-log rho` from concentrating in every right-neighbourhood of `p_c`.
* `fpbs-universal-integrated-sensitivity-route` weakens it again to the
  integrated form `fpbs-integrated-sensitivity-universal`.
* `fpbs-universal-pivotal-rate-contradiction-route` uses the exponential
  version: a collapsed window forces pivotal spikes of exponential order, so
  any genuinely subexponential upper growth rate
  (`fpbs-universal-subcritical-pivotal-growth-rate`) contradicts it via
  `fpbs-collapse-exponential-pivotal-spikes`.
* `fpbs-universal-dyadic-route` goes through the operator side: the dyadic
  size-weighted estimate `fpbs-critical-dyadic-projection-estimate`, the
  proved comparison `fpbs-dyadic-projections-bound-connectivity`, and the L2
  criterion.
* `fpbs-universal-connectivity-operator-route` records the assessment's own
  preferred finishing theorem: nonamenability bounds the critical connectivity
  operator, plus the L2 criterion.

Special cases proved inside the archive are `fpbs-sc-percolation-family` and
`fpbs-ew-window`, an explicit interval for a constructed family. They are
individual geometries, not steps toward the quantifier.

**Refutation doctrine.** A counterexample is not a route into this goal. It
lands as an ESTABLISHED negation claim,
`fpbs-benjamini-schramm-counterexample-exists`, presently an OPEN claim with
its own `## Attempts`; only when that claim is established does this goal take
`refuted_by: [fpbs-benjamini-schramm-counterexample-exists]`. By Lyons the
witness would have to be a nonamenable group of fixed price one, so it would
*satisfy* `fpbs-fixed-price-universal` for its own group rather than
contradict it.

**Decision note, 2026-09-09.** The user forwarded the closing priority verdict
of the archive's session
(`research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md`). This goal
is the PRIMARY affirmative target and Fixed Price is the class-level one. The
stated reasons: the randomness here is prescribed by one model rather than
being an infimum over all measurable graphings; the conclusion is a strict
separation, so a finite bound with a graph-dependent constant suffices and
neither threshold, exponent nor universal gap has to be computed; and several
distinct geometries already deliver the separation, which suggests looking for
their common mechanism. The assessment is explicit that a clean sufficient
condition is not a solved difficult part, and that
`fpbs-nonamenability-bounds-critical-connectivity-operator` is a stronger
conjecture than this goal, not a consequence of nonamenability.

**Cross-links outside the fpbs region.** The cost half of this problem shares
its Gaboriau input with the repository's treeability nodes; see the
cross-links recorded on `fpbs-fixed-price-universal`. There is no percolation
content in that region.

## Attempts

* **Compare adaptive exploration transcripts (2026-09-10).**
  `fpbs-adaptive-exploration-relative-entropy` gives exact information
  cost k(q,c)E_q N for fresh edge queries. Combined with critical spectral
  decay and the fixed-supercritical finite-cluster tail theorem,
  `fpbs-uniqueness-exploration-query-lower-bound` forces conditional
  query cost at least order (q-c)^(-2) per random-walk step under
  uniqueness. **What remains:** a target-directed balanced exhaustive
  search with a strictly smaller proved cost under hypothetical collapse.
  Breadth-first search may have exponential cost in walk length, so its
  finite correctness tests do not provide this upper bound. This is a
  new necessary condition and attack direction, not a completed route.
  The follow-up `fpbs-unit-target-search-ellipse-bound` controls where
  unit-weight search queries edges, but the ellipse can grow exponentially
  with open-path excess. `fpbs-target-search-geodesic-tie-calibration`
  shows unit-weight insertion-order search can already be quadratic in
  distance when all edges are open; weights greater than one avoid that
  particular failure. The censored pilot in `search-geometry.md` supports
  investigating the latter schedules, without providing the needed
  expected-cost bound or a phase determination.
  The further obstruction `fpbs-closed-wall-forces-exponential-search`
  rules out a deterministic polynomial detour bound even for stronger
  target weights. However, `fpbs-bernoulli-wall-branch-budget-summable`
  proves that one family of wall/branch lower certificates has uniformly
  finite expected sum: charging only closed walls and importing an
  all-open volume is invalid. The actual conditional expected-query
  upper bound remains unproved; see `search-barriers.md`.

* **Contract the critical clusters and sprinkle independently (2026-09-09).**
  `fpbs-critical-quotient-sprinkling` preserves the exact conditional bond
  law, infinite-component counts, and a uniform weighted expansion bound.
  `fpbs-critical-quotient-palm-moments` supplies the correct unimodular
  root reweighting: quotient degree has finite first moment but infinite
  second moment. **Where the simple argument dies:** the degree-biased
  exploration mean is infinite, and no independent branching comparison
  is justified. `fpbs-weighted-expansion-allows-zero-uniqueness` separately
  shows that expansion alone allows uniqueness for every positive
  parameter. Its layered graph has no unimodular root law, so it does
  not refute an argument retaining the true critical quotient.
  However, `fpbs-unimodular-critical-quotients-can-have-zero-pu` uses the
  published Angel--Hutchcroft example to show that adding unimodularity,
  finite mean mass and independent sprinkling still does not suffice.
  The unresolved task needs further structure inherited from the FIXED
  Cayley graph; the moment calculation is not a proof of nonuniqueness.
  `fpbs-critical-quotient-environment-gap` now retains one such property:
  the stationary quotient environment inherits the original Bernoulli
  spectral gap. However, `fpbs-quotient-sprinkling-spectral-atom` shows
  that applying this gap to connectivity still permits a small
  uniqueness atom at 1. That comparison does not close the argument.

* **Bound pivotal edges rather than route lengths (response 4,
  `creative-branches.md`, Sections 1.1--1.4).** The finite-volume Russo
  identity `d/dp log a_{n,R}(p) = E_p[N_{n,R} | E_{n,R}]/p` is exact, and a
  uniform bound `E_p[N|E] <= Cn` on `[p_c,p_0]` uniformly in `R` gives
  `a_n(p) <= [rho (p/p_c)^C]^n`, contradicting the FKG lower bound
  `theta(p)^2` that uniqueness would force. The earlier routing obstruction
  does not block this: the bridgeless model on `T_{2r} x Z` has arbitrarily
  long replacement routes and zero pivotal edges. **Where it dies:** the
  exploration run of responses 5--7
  (`docs/exploration-run-research-note.md`, Section 4) builds bounded-degree
  recursive networks `J_k` whose terminals are *adjacent* and whose
  conditional pivotal count grows like `0.0228 k` at a fixed parameter, with
  connection probability staying near `0.992`. Neither adjacency, bounded
  degree, nor rare conditioning controls the count, and a nonamenable
  nontransitive augmentation preserves the obstruction. The successful cases
  are cacti (constant `1+e^(-2)`, optimal) and block graphs, both of which
  have no multiscale cycle overlap.
* **Integrate the sensitivity instead of bounding it pointwise (response 8,
  `exploration.md`, Propositions 2--4).** Only `B(epsilon) < -log rho` is
  needed, and the whole-interval budget `M_{n,R}(1) -> -log rho` is already
  known, so the issue is location rather than total mass. **Where it dies:**
  Proposition 4 shows a collapsed window forces exactly `-log rho` into every
  interval `(p_c, p_c+epsilon)` while each fixed-`n` quantity tends to `0` as
  `epsilon` decreases. The two limits do not commute and no uniformity is
  proved, so the criterion is a reformulation of the collapse, not an
  exclusion of it.
* **Force a contradiction from the exponential scale of the spike (response 9,
  `spectral-spike.md`, Sections 4--7).** Theorem 6.1 proves that collapse
  requires conditional pivotal counts of order `n exp(alpha n)` for every
  `alpha < lambda_0/2`. **Where it dies:** Section 6 states that (6.2) is not
  a contradiction, since the witnessing radius `R_n` is unbounded and
  `N_{n,R} <= |E(B_R)|` permits that growth; the needed upper estimate (6.5)
  is unproved. Section 7 supplies the reason for pessimism: a monotone FIID
  partition model on the same graph reproduces the whole spectral jump,
  including a logarithmic-derivative peak at exactly rate `lambda_0/2`, so no
  argument using only the spectral decomposition can exclude the scenario. The
  atom of mass `theta(p)^2` at `1` in the uniqueness-phase decomposition (4.4)
  can be arbitrarily small and still dominate long-time sampling.
* **Prove the dyadic operator estimate (response 4, Section 2.2; response 8,
  Sections 3--4).** On regular trees the size-shell cluster-averaging
  projections satisfy `||Q_N|| asymp N^(-3/2)`, with an exact closed formula,
  so the summability that would bound `T_{p_c}` holds there with room to
  spare. **Where it dies:** Theorem 6 of `exploration.md` builds a group
  equivariant factor of iid on the nonamenable graph `T_4 x Z` with all
  clusters finite, infinite susceptibility, and divergent dyadic sum. So
  nonamenability, critical-style finiteness and FIID admissibility do not
  imply the estimate; some property specific to independent bond percolation
  must be used. A root-overlap bound is a trace moment and not an operator
  norm, so it cannot substitute.
* **Use cost (Lyons).** Closed on the non-fixed-price-one side and open on the
  other; see `fpbs-fixed-price-one-percolation-kernel`, whose `## Attempts`
  records why the quantitative cost bound of response 1 degenerates to
  `0 <= 0` under threshold equality.
* **Refuting the conjecture** is represented by
  `fpbs-benjamini-schramm-counterexample-exists`, not by a route into this
  goal.
