# Swarm note: fpbs-correlated-reuse-flags-removable, 2026-09-16

Agent: swarm-fpbs-correlated-reuse-flags-re. The hole worked was the target
itself, `fpbs-correlated-reuse-flags-removable`, locked at about 02:39 UTC
with a 180 minute TTL. Nothing was committed.

## 1. Setup

The target asks for near-optimal source routing plans whose group-correlated
reuse flags can be removed without increasing completed cost. By the
September 12 scope audit on the node, for a fixed factor map pi: Y -> X this
is equivalent to C(X) = C(Y). Over all free factor maps of a group it is
equivalent to Fixed Price for that group, and on the product projection
a x b -> b it is equivalent to C(a) = C(b). The variational identities give
C(X) - C(Y) = inf [(B - C(Y)) + J_pi]. Any plan property P that lifts from the
base and forces J_pi -> 0 gives an equivalent restatement. The audit left
one question explicitly open. The fixed-cutoff uniform-integrability (UI)
form of `fpbs-binary-entropy-traffic-tail-bound` implies preservation. Is it
implied by preservation, or is it a priori stronger?

This session answers that question (Section 3). It does not settle the
target.

## 2. Literature gate

Search date: 2026-09-16.

In the first part of this session I checked recent cost and fixed-price
items against the repository. I found no preprint announcing a resolution of
Fixed Price or of the reuse-removal statement. The newest relevant items are
already recorded in the graph:

* Khezeli, arXiv:2509.08325 (products of infinite groups have fixed price
  one), imported as `fpbs-khezeli-products-have-fixed-price-one`;
* Bevilacqua--Bowen, arXiv:2510.05459, cited in
  `fpbs-normal-subgroup-bounded-cost-fixed-price-one` and
  `fpbs-hyperbolic-3-manifold-groups-fixed-price-one`;
* Poulin--Wrobel, arXiv:2606.23506v1, with a source record dated 2026-09-11;
* Slutsky, arXiv:2607.20273v1 (July 2026), which lists the universal problem
  as open, recorded on `fpbs-fixed-price-universal`.

After the context break I tried a final sweep for August--September 2026
preprints, and it could not be completed. The session web-search budget was
exhausted, and the arXiv export API returned HTTP 429 or 503 and timed out.
This gate therefore has a gap for preprints posted after the repository's
last dated recheck, and the referee should repeat that sweep. No citation
below depends on an unfetched source except where marked:

* The Borel maximal-independent-set construction is attributed generically
  to Kechris--Solecki--Todorcevic (1999). It was not fetched and no theorem
  number is asserted. The artifact proves the case used.
* Lyons--Pichot--Vassout (arXiv:0711.0393) and Pichot--Vassout
  (arXiv:0903.0911) are mentioned only as related background, taken from
  repository citations and not fetched. Whether Theorem 1 below is implicit
  in them is unverified.

The congestion inequality is a max-flow/min-cut count and may well be
folklore. No novelty is claimed.

## 3. What was proven

This session adds the new claim `fpbs-cost-one-plans-have-heavy-traffic-tails`
with route `fpbs-cost-one-plans-have-heavy-traffic-tails-proof`. The full
proof is in
`research/artifacts/fpbs-cost-one-plans-have-heavy-traffic-tails-2026-09-16.md`,
and the finite replay is in
`experiments/fpbs-cost-one-plans-heavy-traffic-2026-09-16/`.

**Theorem 1.** Let Gamma be infinite and finitely generated, S a finite
generating set, and h_S the right edge Cheeger constant. For every finite
routing plan D for S on a free p.m.p. action, with arbitrary labels, and
every real T >= 0,

    h_S <= (T+1)(B(D) - 1) + Tail_T(D),   Tail_T = sum_j integral Q_j 1_{Q_j>T},  Q_j = (k_j-1)_+.

The proof has four steps.

1. Add a direct copy for each uncovered request. B and all tails are
   unchanged, and the used graph then connects each orbit.
2. Take a Borel maximal 2R-separated marker set by countable colouring and
   greedy selection, and form Voronoi cells with Borel tie-breaks. The cells
   are finite and connected with at least R+1 points. Their parent trees have
   measure 1 - nu(markers) >= 1 - 1/(R+1). The copies crossing between cells
   therefore have measure at most B - 1 + 1/(R+1).
3. By freeness a cell is a finite subset of Gamma. Mass transport then shows
   that generator requests leaving their cell have measure at least h_S.
4. Each leaving request uses a crossing copy. Identity (2.3) of the
   conditional-traffic artifact and the pointwise bound
   k <= T+1+Q 1_{Q>T} finish the proof. Let R -> infinity.

For nonamenable Gamma this gives:

* **(a)** traffic bounded by M forces B >= 1 + h_S/M, so peak traffic is at
  least h_S/(B-1);
* **(b)** if B(D_n) -> 1 then liminf Tail_T(D_n) >= h_S for every T;
* **(c)** sum_j integral Q_j^2 >= (h_S - eps)^2/(4 eps), where eps = B - 1;
* **(d)** a moving cutoff with Tail_{T_n} -> 0 needs T_n >= h_S/(4(B_n - 1)),
  so the criterion T_n H_n -> 0 needs H_n = o(B_n - 1).

**Strictness.** Take F_2 x Z, which has fixed price one by Khezeli. Every free
factor map preserves cost, and the variational identity supplies plans with
B -> 1 and J -> 0. By (b) no source-near-optimal sequence has UI repeated
traffic. So the fixed-cutoff UI form is strictly stronger than preservation.
It can never be verified over a cost-one source of any nonamenable group.
This answers the scope audit's open question.

The finite replay ran 160 random plans over Z/40, Z/12 x Z/6, S_4 and A_5 in
exact arithmetic. It passed every counting step: augmentation, cells, parent
trees, crossing measure, the pointwise bound, and the chain up to the
boundary term. It cannot test Lemma 6, since finite groups have h_S = 0.

Validation exit codes and the unlock are recorded in Section 5.

## 4. Approaches and exactly where each dies

I considered six approaches. The first four target the claim itself. The last
two concern the entropy-tail route, which is the only positive criterion now
in the graph.

1. **Restricted families.** The first idea was to prove the target first for
   special extensions and then glue. The families that are easy to reach are
   already in the graph:
   * independent noise over a fixed base, in
     `fpbs-bernoulli-noise-does-not-change-cost`;
   * uniform finite fibers at source cost one, in `fpbs-finite-fiber-cost-bound`;
   * revealing the flags on an intermediate factor, in
     `fpbs-reuse-flag-localization-preserves-cost`.

   The approach dies at gluing. The target's own Attempts section records
   that the localization theorem keeps the flag information instead of
   forgetting it. Group-coherent observations inside the forgotten coordinate
   are not conditionally independent, so the noise simulation does not apply
   to them. I found no family that is strictly larger than these, still open,
   and not already equivalent to C(X) = C(Y) for the groups involved.

2. **Furstenberg--Zimmer towers.** Climb from X to Y through compact
   extensions and relatively weakly mixing steps. Compact steps are finite
   or profinite fibers (see approach 3). The approach dies at the relatively
   weakly mixing step. No cost handle on relative weak mixing is recorded in
   the repository, and I know of none in the literature. Importing a
   structure theorem for non-ergodic or non-amenable relative extensions
   would also be an import risk.

3. **Profinite sources.** Suppose Y is an increasing limit of uniform
   q_r-point extensions Z_r of X.
   * Section 10 of the conditional-traffic artifact gives C(Z_r) decreasing
     to C(Y).
   * `fpbs-finite-fiber-cost-bound` gives C(X) - 1 <= q_r(C(Z_r) - 1).

   The approach dies because q_r -> infinity, so these two facts together
   say nothing even when C(Y) = 1. Exact equality at each stage would need
   finite-index multiplicativity for specified free actions. The
   finite-fiber artifact records this as Furman's survey Question 4.11 and
   proves it equivalent to universal preservation for finite fibers. It is
   open, and this session did not advance it.

4. **Route-length divergence.** The idea was to use
   `fpbs-quantitative-routing-tail-bound` to show that source-near-optimal
   plans need long routes, and to trade length for correlation. It dies for
   two reasons. That node controls invariant spanning subgraphs of a fixed
   Cayley graph, while plans here use arbitrary group labels, so ball growth
   in the used graph is not tied to the word metric. And the bound is not
   uniform in the plan. Replacing length by congestion is what produced
   Theorem 1. Congestion is label-independent because the argument only
   needs finite cells of the used graph and freeness.

5. **Fixed-cutoff UI form of the entropy-tail criterion.** Show that
   near-optimal source plans can be chosen with sup_n Tail_T(D_n) -> 0 as
   T -> infinity, then apply `fpbs-binary-entropy-traffic-tail-bound`. This
   is now provably dead over every cost-one source of every nonamenable
   group, by Corollary 2(b): Tail_T(D_n) stays at least h_S - o(1) for every
   fixed T. For infinite amenable groups every free action has cost one. This
   is the standard Ornstein--Weiss hyperfiniteness together with Levitt's
   cost-one theorem; I did not re-fetch it and assert no theorem numbers.
   So the target is trivial there. The UI form is therefore either
   unnecessary or unavailable wherever the source has cost one. Sources of cost above one are not touched
   (Section 5).

6. **Moving-cutoff form.** Take T_n -> infinity with T_n H_n -> 0 and
   Tail_{T_n}(D_n) -> 0. This survives, but Corollary 2(d) sets a rate.
   Over a cost-one source it needs T_n >= h_S/(4(B_n - 1)), hence the
   binary conditional entropy H_n of the reuse flags must be o(B_n - 1). It
   dies at construction: no mechanism turns an arbitrary near-optimal plan
   into one whose flags are that close to deterministic given the base. The
   lifted-plan paragraph of the artifact shows why this is not
   contradictory. When C(X) = C(Y) = 1, lifted near-optimal base plans have
   H = 0, and their traffic tails grow at least like h_S/(B_n - 1). So
   heavy traffic and small entropy can coexist. Producing such plans from
   the source side is the target in another guise.

## 5. What remains open

* **The target itself is still open.** Theorem 1 does not prove or refute
  it. It only removes one sufficient condition, and only over cost-one
  sources. The target stays equivalent to C(X) = C(Y) for the given factor
  map.
* **Sources of cost above one.** Take a source with C(Y) > 1 and plans with
  B(D_n) -> C(Y). Inequality (2.1) gives
  Tail_T(D_n) >= h_S - (T+1)(C(Y) - 1) - o(1). That is positive only for
  T + 1 < h_S/(C(Y) - 1), so it says nothing about T -> infinity. Whether
  the fixed-cutoff UI form can hold over such sources is open, and so is
  whether some other congestion bound blocks it.
* **Moving cutoff.** Over a cost-one source of a nonamenable group, a proof
  of the target through `fpbs-binary-entropy-traffic-tail-bound` needs
  source-near-optimal plans whose binary flag entropy H_n is o(B_n - 1).
  Such plans are not known to exist, and there is no construction that
  produces them from arbitrary near-optimal plans.
* **Countable, non-finitely-generated groups.** Theorem 1 is stated for
  generator requests of a finitely generated group. The finite-prefix demand
  convention for general countable groups has a moving demand set. I did not
  work out an analogue with a relative Cheeger constant.
* **Route length with arbitrary labels.** Whether source-near-optimal plans
  must also have long routes, in any label-independent sense, is not
  addressed. Theorem 1 forces congestion, not length.
* **Novelty.** Whether (2.1) appears implicitly in Lyons--Pichot--Vassout or
  Pichot--Vassout, or is folklore, is unverified (Section 2).

**Validation and lock.** Each `check.sh` run covered the three research
paths: claim, route and artifact.

1. The first run exited 0. It reported the new claim as established over its
   two required nodes, with no findings naming these files.
2. I then fixed the wording of the marker construction in Lemma 5 of the
   artifact, so it now states the point-separating family precisely. A rerun
   was killed by my own 600 s wrapper while it waited for a check slot.
   Restarted without the wrapper, it exited 0.
3. After adding a `distinct_from` entry for
   `fpbs-sparse-reuse-signal-near-cost-one`, I ran `check.sh` once more. Its
   exit code is the `check_exit` of the final report.

`bin/cairn search --similar` found no near-duplicate claim. The closest
related node is `fpbs-sparse-reuse-signal-near-cost-one`. It notes that a
hypothetical cost gap would force large relative traffic and that no uniform
traffic bound is proved. Theorem 1 shows that for ordinary plans on
cost-one sources of nonamenable groups, a uniform traffic bound is impossible
with no gap assumed. After validation the lock was released with
`bin/cairn unlock`. Nothing was committed.
