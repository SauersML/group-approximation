---
rg: 2
id: fpbs-benjamini-schramm-universal
kind: claim
title: Every nonamenable locally finite Cayley graph has a Bernoulli bond nonuniqueness interval
root: true
goal: true
artifacts:
  - research/artifacts/fpbs/docs/global-pivotal-tails-and-volume-defect.md
  - research/artifacts/fpbs/docs/direct-bs-new-results.md
  - research/artifacts/fpbs/navigation.md
  - research/artifacts/fpbs/docs/cluster-contact-mergers.md
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

**Decomposition supplied by the archive and subsequent work.** Eight live routes
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
* `fpbs-universal-optimistic-certificate-route` combines the established
  query strong converse and the sound optimistic search with the OPEN
  construction `fpbs-universal-optimistic-certificate-budget`. That
  construction must supply subexponential connection success below the
  information budget under hypothetical collapse. This puts the missing
  algorithmic estimate on Cairn's frontier, rather than only in prose.

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

* **Derive nonuniqueness from the critical Bernoulli law plus soft
  supercritical axioms (2026-09-17).** The idea was to feed critical-phase
  information (sharpness, no critical percolation, the critical L2 bound) into
  axioms that hold for every monotone invariant family: invariance,
  ergodicity, insertion tolerance, and continuity of `theta` at `p_c`.
  **Where it dies:** `fpbs-soft-collapse-iff-invariant-sparse-spines` builds
  a monotone invariant ergodic insertion-tolerant family on the Cayley graph
  itself. It equals Bernoulli for all `t <= p_c` and has a unique infinite
  cluster for every `t > p_c`, with `theta -> 0`. The construction runs
  whenever invariant sparse spines exist, for example over any surjection to
  `Z` with finitely generated kernel. That includes `T_3 x Z`, hyperbolic
  fibred 3-manifold groups and `F_2 x Z`, all of which have a genuine window.
  On the hyperbolic ones `||T_{p_c}||_{2->2} < infinity`, yet the family has
  `||T_t||_{2->2} = infinity` for every `t > p_c`. So the continuation step
  from `p_c` to `p_c+eps` must use a supercritical Bernoulli property the
  family lacks: product structure (Russo, BK), possibly Harris--FKG or deletion
  tolerance. Extending the obstruction to every fixed-price-one group is
  exactly the invariant-spine question.

* **Quantify global pivotals before passing to finite balls (2026-09-12).**
  `fpbs-global-pivotal-tail-at-uniqueness` proves exponential global
  connection-pivotal tails, uniform in both endpoints at each fixed
  uniqueness parameter, by exact bridge-closing surgery. The new
  `fpbs-pivotal-volume-defect-criterion` proves that finite-ball counts
  eventually agree almost surely with the global count and identifies
  convergence of conditional means with uniform integrability of the
  nonnegative boundary-bypass excess. These strengthen the dangling-bridge
  input. The live growth route still needs both near-critical control of
  the constants and uniform finite-volume excess bounds; almost-sure
  stabilization supplies neither estimate.

* **Final thinning, free-energy, and subgroup checks (2026-09-10).**
  Sections 7--9 of `docs/direct-bs-new-results.md` record the remaining
  follow-ups. Thinning bounds the probability of short connections from
  above; the available detour theorem assumes the OPEN L2 threshold
  separation. Free-energy regularity does not directly detect mergers
  of infinite clusters, and finite-ball mean cluster counts need not
  converge to the infinite rooted free energy. The subgroup-relativization
  theorem's exclusion of uniqueness at p_u explicitly permits zero
  infinite clusters. None of these checks discharges a root premise.
  After three consecutive unsuccessful attempts the session research goal
  was marked blocked; the mathematical claim remains OPEN, not refuted.

* **Test two-cluster and intrinsic-growth inputs (2026-09-10).**
  Sections 5--6 of `docs/direct-bs-new-results.md` retain the finite-cluster
  restriction in the two-ghost inequality and prove the exact order of
  limits for two large distinct clusters in free finite volumes. A regular
  tree shows that those limits cannot be exchanged. Universal small
  intrinsic growth near criticality also gives no contradiction to
  uniqueness without a bound on connecting-path lengths; the stronger
  growth results assume the still-OPEN L2 condition. No root premise is
  discharged by these checks.

* **Use the September weighted-isoperimetry theorem (2026-09-10).**
  Hartarsky--Severo--Teixeira, arXiv:2609.07768v1, concerns percolation
  existence, including a different Benjamini--Schramm question about
  p_c<1. `fpbs-critical-quotient-small-profile-obstruction` shows its
  profile hypothesis fails for weak sprinkling on the actual critical
  quotient because infinitely many singleton cells remain. Section 3 of
  `docs/direct-bs-new-results.md` also identifies exactly what exterior
  wiring adds: connections between distinct infinite clusters. Its
  finite-volume connectivity estimate therefore cannot be read as a
  free two-point bound without an additional argument. The August
  cluster-graphing note arXiv:2608.06644v1 supplies a new exposition of
  critical finiteness, not a right-neighbourhood nonuniqueness theorem.

* **Track growth and mergers separately (2026-09-10).**
  `fpbs-cluster-contact-merger-balance` gives an exact finite-state
  balance: quotient triangles create parallel contacts and subsequent
  mergers remove them. However,
  `fpbs-contact-dispersion-sign-obstruction` shows that the proposed
  effective-neighbor statistic has opposite initial drifts even on two
  nonamenable Cayley graphs of the same degree. A merger between other
  clusters can lower the root statistic without growing its cluster.
  The calculation supplies no near-critical sign, infinite-volume
  moment control, or implication to threshold separation. See
  `docs/cluster-contact-mergers.md` for the exact identities and scope.

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
  The sharpened `fpbs-bounded-query-connection-strong-converse` now
  shows that below the information budget, successful certificates are
  exponentially unlikely. The follow-up
  `fpbs-uniqueness-query-quantiles-and-tube-width` rules out explaining
  the cost purely by rare expensive searches and gives a necessary
  walk-tube width. A weaker sufficient construction would be a capped
  search below that budget with subexponential success under collapse;
  it would not need to decide every connection. Section 5 of
  `query-strong-converse.md` states this still-unproved construction
  precisely. Neither uniqueness nor the new estimates supplies it.
  A finite-branch accounting shortcut for the current priority search
  is also insufficient: Corollary 1.1 of `search-barriers.md` shows
  that its exponential wall obstruction already has uniform positive
  expansion and an open four-cycle through every open edge. The missing
  estimate must control exploration in the part with no bridges, not
  just the sizes of finite dangling pieces.
  A different candidate, `fpbs-optimistic-search-certified-growth`,
  replans shortest paths using only known closed edges and certifies
  a growing tree. `fpbs-optimistic-search-linear-wall-cost` proves
  that it crosses the same wall in exactly 5m+4 queries, overcoming
  that schedule-specific obstruction. The next missing estimate is
  a Bernoulli bound on the certified vertices it explores, with no
  substitution of full ball volume for walk length; see Section 5 of
  `optimistic-search.md`. The finite pilot does not supply this estimate.

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
* **Pass to finite expander approximants and read `p_u` off a giant-component
  uniqueness window (2026-09-17).** The idea was to prove a finite-graph
  statement on large-set expander graphs `G_n` converging locally to the
  Cayley graph and take the limit. **Where it dies:**
  `fpbs-expander-approximant-giant-data-is-glued`.
  (A) By Alimohammadi--Borgs--Saberi Theorem 1.1, `|C_2|/n -> 0` at every `p`,
  so the window is empty even for random regular graphs converging to `T_d`.
  (B)/(C) Every bounded-separation connectivity or MST observable converges to
  the glued/wired law, in which two infinite clusters count as connected.
  (D) The only finite observable that sees `p_u` is the two-scale defect
  `lim_R lim_n s_n(p,R)`. It equals the distinct-infinite-cluster integrand of
  `fpbs-msf-excess-equals-nonuniqueness`, so the scale shift is an equivalence
  with no new estimate.
* **Close the sw-008 loophole with finite energy and FKG (2026-09-17).** The
  idea was that a contradiction from `p_u = p_c` might still follow from the
  soft supercritical toolbox once deletion tolerance and Harris–FKG are added
  to (S1)–(S4). **Where it dies:**
  `fpbs-finite-energy-fkg-collapse-over-central-z2-slabs`. Every Cayley graph
  of a nonamenable group with a central `Z` inside a `Z^2` carries a
  collapsing family with all of these properties. The spine is built from
  thinned amenable slabs, each keeping only its Burton–Keane giant, joined by
  all-or-nothing connectors that recur along the central direction.
  `F_2 x Z` has a window for some generating set. So the continuation step
  from `p_c` to `p_c + eps` must use one of four things: independent
  increments (BK, Russo, sprinkling, differential inequalities), mixing,
  uniform finite energy, or FIID/cost structure. The last is useless on this
  fixed-price-one class.
* **Mixing, uniform finite energy and FKG (2026-09-17).** This asks whether
  the three remaining soft properties force a window. **Where it dies:**
  `fpbs-fiid-uniform-finite-energy-fkg-collapse-family`. Every Cayley graph in
  the same class carries a collapse family with all of these properties at
  once:
  * it is FIID, hence mixing of all orders;
  * every edge has conditional probability in `[t, t+(1-t)q]`;
  * it is Harris–FKG and contains `xi_t`.

  The spine consists of iid thin planar sticks at infinitely many scales,
  thinned by independent edge marks. The sticks are glued across scales by
  Harris and across cosets by recurrence along the central direction.
  Uniqueness comes from indistinguishability with marks. Of the four
  ingredients listed above, only independent increments of the product law
  above `p_c` remain: BK/Reimer, Russo, and upper-bound differential
  inequalities.
* **Intrinsic-radius kernels: BK in the radius, not in the parameter
  (2026-09-17).** Route `fpbs-universal-intrinsic-l2-rate-route`.
  - **Established part** (`fpbs-intrinsic-l2-rate-closed-zero-set`). Define
    `T^(R)_t(u,v) = P_t(d_omega(u,v) <= R)`. By BK,
    `T^(R+R') <= T^(R) T^(R')` entrywise. So the rates
    `Lambda(t) = inf_R R^(-1) log ||T^(R)_t||_(2->2)` and
    `lambda_1(t) = inf_R R^(-1) log E_t|B^int_R|` are infima of continuous
    functions. They are therefore upper semicontinuous and right-continuous.
    Sharpness puts `[0,p_c)` in their zero sets, and the zero sets are closed,
    so both rates vanish on `[0,p_c]` on every nonamenable Cayley graph, with
    no critical `l2` input. A linear chemical stretch constant `K` at `t`
    gives `Lambda(t) >= log(gr)/(2K)`. So the stretch constant diverges at
    `p_c+` universally.
  - **Open side.** A chain of sufficient conditions, each stated only for
    `t > p_u`: (UCS) `fpbs-uniform-chemical-stretch-above-pu` implies (IL2)
    `fpbs-intrinsic-l2-rate-bounded-below-above-pu`, which implies (IL1)
    `fpbs-intrinsic-growth-rate-positive-at-pu`, which implies `p_c < p_u`.
    (UCS) and (IL2) can fail on graphs that have a window.
  - **Where it stops.** (UCS) needs linear chemical distance in the uniqueness
    phase, which is not available on general nonamenable graphs (there is no
    Antal--Pisztora renormalization). It also needs a merge-scale estimate at
    `p_u+`.
  - **Class killed.** Arguments that give uniform stretch above a threshold
    `q` from inputs that `q = p_c` also satisfies die at item 6 of the
    established claim.
* **Rate-based continuation and product structure above `p_c` (2026-09-17,
  w3-123).** The rate step was to choose `n(t)` so the spine density decays
  fast, and to show that `theta` and local laws match Bernoulli. That is
  already (H3)/(H4) of `fpbs-sharp-dominating-collapse-over-sparse-spines`.
  The new node `fpbs-quenched-bk-russo-collapse-operator-gate` pushes the
  obstruction to product-structure tools. The same family is:
  * a quenched product measure given its spine environment, so Harris-FKG,
    BK-Reimer and Russo hold for every environment;
  * annealed Russo off a countable jump set;
  * exact annealed independent sprinkling;
  * BK at bounded range up to `f(t)`.

  It still collapses on graphs with `||T_{p_c}|| < infinity`, for example
  hyperbolic mapping tori. **Where it dies:** the one product input it lacks
  is the annealed operator inequality (G). Its entrywise form is
  `dT <= C T J T` plus jump atoms `m_k T J T`, with `C` integrable and
  `sum m_k` finite. Theorem 2 there integrates (G) with atoms from
  `||T_{p_c}||` to a window. So quenched diagrams must average to bounded
  multiples of `T J T`, uniformly in volume. The node proves only that
  interval factorization (a) or jump factorization (b) fails. Deciding which
  one fails is the next step.
* **Worst-pair connectivity rate, weaker than the sphere-rate kernel
  (2026-09-17, belief breaker).**
  - **Established side.** `fpbs-worst-pair-connectivity-rate-kernel` has an
    import-free proof using Harris-FKG and Fekete. The rate
    `gamma(p) = lim -(1/n) log min_(v in B_n) tau_p(o,v)` exists and is
    nonincreasing and left-continuous. Uniqueness forces `gamma = 0`, and
    `g(p) >= log gr - gamma(p)`. Hence
    `(EG) => (G) => (K') [g(p) < log gr] => (K) [gamma(p) > 0] => p_c < p_u`,
    each at one `p > p_c`.
  - **Belief change.** The two last-missing sphere-rate holes (G) and (EG) are
    strictly stronger than needed. On `T_d`, (K') and (K) hold on all of
    `(p_c,1)`, while (G) holds only on `(p_c,1/sqrt(d-1))`. So an obstruction
    to (G) near `p_c` does not threaten the sphere route. The route
    `fpbs-bs-via-worst-pair-connectivity-rate` dominates
    `fpbs-bs-via-sphere-two-point-rate`.
  - **Where it stops.** The OPEN kernel is
    `fpbs-worst-pair-connectivity-rate-positive-above-pc-universal`.
    - Hutchcroft's bound `kappa_(p_c)(n) <= gr^(-n)` gives
      `gamma(p_c) >= log gr` (recalled, not load-bearing). So a collapse must be
      a jump of `gamma` of size at least `log gr` at `p_c+`.
    - Finite-radius certificates bound the supermultiplicative `kappa` only
      from above.
    - The missing inputs are expected extrinsic growth of infinite clusters
      strictly below `gr`, and a subexponential finite-cluster susceptibility,
      at one `p > p_c`.
* **Continuous spine activation (2026-09-18, w5-123).** This settles the
  (a)/(b) question left by `fpbs-quenched-bk-russo-collapse-operator-gate`.
  `fpbs-continuous-activation-collapse-family` gives a collapse family, with
  the same (S1)-(S4) and (H1)-(H5), in which spine edges switch on one at a
  time, at continuously distributed times. The spines are interpolated
  through invariant geodesic forests with product-of-uniform levels.
  - Every quenched jump is a single edge of weight at most `1`.
  - Every local annealed probability, and every `T^Lambda`, is absolutely
    continuous in `t`, so there are no annealed jump atoms.
  - Collapse families do not need infinite total jump weight. However, the
    quenched density must exceed `p_u` somewhere just above `p_c`
    (Proposition 3 there).

  **Where it dies:** (G) still fails, now in its density term alone. The
  ratio `dT^Lambda/dr : T^Lambda J T^Lambda` is integrable for each fixed
  `Lambda`, but not uniformly in `Lambda` (non-equicontinuity in volume). So
  the jump estimate (b) is not load-bearing. Next: split the density into the
  off-spine Russo part and the activation part, and decide whether the Russo
  part alone factorizes against `T J T`.
* **Annealed pivotal factorization and the reduced gate (2026-09-18,
  w6-123).** `fpbs-annealed-pivotal-factorization-off-spine-bridges`: in any
  quenched product over a label-independent environment, the off-spine Russo
  part satisfies `R <= T J beta + beta J T <= 2 T J T` uniformly in `Lambda`,
  up to pivotals that bridge two pieces of `Z ∩ Lambda`. The reason is that
  off bridges one separated cluster avoids the spine, so it is a pure Bernoulli
  cluster and annealing factorizes. In spine-augmented volumes `Lambda ∪ Z_t`
  there are no bridges, since the spine is connected. There
  `D^R <= 2 (t-s) X J X`, and the activation part is at most the explicit
  kernel `beta_s (S_t - S_s) beta_s`, with `S` the spine two-point function.
  `fpbs-spine-increment-activation-gate` reruns the Bihari gate over this
  exhaustion, with an atomless right-endpoint measure. So (G) reduces to the
  single fully annealed inequality (AG*): `beta (S_t - S_s) beta <= kappa_A X J X`.
  Every collapse family over a connected spine grown from `∅` violates it,
  the continuous-activation family included.

  **Where it dies:** the Russo part is not the obstruction. The whole failure
  is the Bernoulli-sandwiched spine increment. Heuristically this is
  `∫ dS/S = infinity`, because `S_{p_c} = 0`. Next: prove the log law
  `kappa_A((s,t]) >= c log(m(t)/m(s))`, and identify an invariant input that
  forces (AG*).
* **The log law for volume-uniform activation gates (2026-09-18, w7-123).**
  `fpbs-volume-uniform-activation-gate-log-law`: test the activation gate on
  two far-apart edges `{u,w}`, `{v,w'}`. There `D^A(u,v) >= s^2 ΔPsi` and
  `X J X(u,v) <= 4 mu Psi(t)`, where `Psi` is the probability that the spine
  meets both edges. A spine vertex at distance `4` gives `Psi(y) >= m(y)/d^4`.
  Chaining intervals on which `m` grows by the factor `4 d^4` gives
  `kappa_A((s,t]) >= c log(m(t)/m(s)) - c'` for any gate holding over all
  two-edge volumes. This covers (AG), (AG*) and the full gate. It holds for
  every connected invariant spine with continuous density, with no collapse
  or critical-L2 input.

  **Where it dies:** every volume-uniform activation input dies at the birth
  of any spine (`kappa_A = infinity` near `s*`), whether or not the family
  collapses. So the failure is not evidence about uniqueness. A correct input
  must be exhaustion-specific. Open: the log law along a fixed exhaustion,
  where `X J X` carries unbounded spine-routed mass.
* **The exhaustion norm law (2026-09-18, w8-123).**
  `fpbs-exhaustion-activation-gate-norm-law`: run Theorem 1 of the reduced
  gate in one exhaustion volume `W` at a time. The spine forces
  `||X^W_t|| >= m(t)^2 |W|` (it is connected). First/last-spine-vertex BK
  gives `||X^W_s|| <= B + B^2 m(s)|W|`, with `B = ||T^Bern_{t_1}||` finite
  below `p_{2->2}`. So each volume charges a fixed mass `c_0` to the
  density window `[1/|W|, sqrt(A/|W|)]`. Summing over volume scales gives
  `kappa_A = infinity` at every spine birth, along every exhaustion. The rate
  is log-log in general and log under decorrelation.

  **Where it dies:** the exhaustion form of (AG), and of (AG*) and the full
  gate, fails for every connected invariant spine born from `∅` when
  `p_c < p_{2->2}`, whether or not the family collapses. A sparse exhaustion
  lowers the rate but not the divergence. Activation gates of the form
  `D^A <= kappa X J X` are therefore dead as a separator of uniqueness.
  Surviving: inputs not bounded by the norm of `X J X`, and the Br route
  (`Br <= C T J T` over plain volumes).
* **Refuting the conjecture** is represented by
  `fpbs-benjamini-schramm-counterexample-exists`, not by a route into this
  goal.
