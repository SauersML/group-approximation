---
rg: 2
id: unique-games-hard-on-non-sse-grassmann-constraint-graphs
kind: claim
title: Gap-UG[1 - eta, delta] is NP-hard already on unique games whose constraint graph is a Grassmann 2-to-1 constraint graph, which has small non-expanding zoom-in sets, so UGC could be proved without any small-set-expanding instance
distinct_from:
  small-set-expansion-hypothesis: that is hardness of expansion on SSE-type instances, equivalent to UG on SSE graphs; this asks for UG hardness exactly on graphs that are not small-set expanders.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that claim implies this one by taking the orientation lift, whose constraint graph is the source Grassmann graph; this one allows any unique constraints on that graph and needs no selector.
---

**OPEN.** This is heretic denial H3.

**Assumption denied (A3).** The HOT lanes attack UGC and SSEH through the same
reductions and the same SSE-type instances. Examples are noisy-cube and
long-code compositions, the RST equivalence, and the kills
`sse-reductions-need-high-threshold-rank-on-both-sides` and
`lifts-over-multiscale-expanders-expand-unless-ug-value-large`. The denial is
that UG hardness lives on Grassmann graphs, which are not small-set expanders
because zoom-in sets `{L : x in L}` expand poorly. That is the counter-signal
recorded in the KMS analysis: UGC may be true while SSEH is false.

**Claim.** For every `eta, delta > 0` there is a polynomial-time reduction from
3SAT to unique games whose constraint graphs are (weighted) Grassmann 2-to-1
constraint graphs of the DKKMS shape. The reduction satisfies:
- YES instances have value `>= 1 - eta`;
- NO instances have value `<= delta`.

**Structure.**
- Via `view-local-branch-selectors-are-gauge-blind`, any such reduction that
  orients the source 2-to-1 constraints with parity-faithful views fails at
  completeness one half. The unique constraints must therefore be computed with
  parity leakage, or they must not be orientations of the source constraints.
- The claim is falsifiable algorithmically. One falsifier is a polynomial-time
  algorithm for UG at `(1 - eta, delta)` on these constraint graphs, for example
  one exploiting global hypercontractivity or the zoom-in non-expanding sets
  (cf. the Bafna--Minzer line on unique games over globally hypercontractive
  graphs, not verified here against Grassmann weights). The other is a proof that
  the relevant threshold rank of these graphs is polylogarithmic. That would
  make the subexponential Arora--Barak--Steurer algorithm polynomial-time on
  them.
- A proof would separate the UGC route from SSEH in the graph and invalidate the
  implicit premise that UGC hardness needs SSE-type outputs.

## Attempts

* **Orientation lifts with parity-faithful views (2026-09-18).** **Dead at
  completeness one half.** The oblivious split
  (`unique-games-hard-at-completeness-one-half`) and
  `view-local-branch-selectors-are-gauge-blind` both stop at `1/2`. The
  remaining attack is a global selector
  (`parity-leaking-branch-selectors-reach-near-perfect-completeness`). The
  algorithmic falsifier through global hypercontractivity is deferred until the
  Grassmann weights are checked against that hypothesis.
* **2026-09-18, swarm-0917-w9-w9-ugc-break (reframing): the deferred
  global-hypercontractivity falsifier was resolved and the hole decomposed.
  Status stays OPEN.**
  * **Bafna--Minzer does not falsify this claim as stated, for two independent
    reasons.**
    - *Host.* Their Theorems 1.6--1.8 cover `Grass(n, l)`, `J(n, l, alpha l)`
      and HDX walks. The hosts here are the DKKMS 2-to-1 constraint graphs,
      which depend on the outer 3LIN instance and are none of these.
    - *Constraints.* They cover only Affine-UG over `Z_q` (Definition 1.4).
      Their footnote 2 says the KKMO reduction does not preserve the host.
  * **What BM does reach, exactly.** On any host, a unique game is a union of
    group-shift games on the same graph exactly when its holonomy group acts
    regularly on each orbit, and it is Affine-UG exactly when that action is
    cyclic. This is `unique-games-reduce-to-shifts-over-their-holonomy-group`.
    Consequently, on BM hosts every instance with cyclic holonomy is solved at
    every constant completeness (Corollary BM). If this claim is ever moved to
    a BM-type host, its instances must have non-cyclic holonomy on some orbit.
    The remaining algorithmic question is
    `general-unique-games-easy-on-globally-hypercontractive-graphs`, with rungs
    R2 (regular, for example `F_2^N` shifts), R3 (solvable, for example
    `AGL(m, 2)`) and R4 (full `S_k`).
  * **Shift instances are not excluded a priori.** By
    `ugc-is-equivalent-to-affine-ugc`, under UGC hard instances can be taken to
    be bipartite `Z_q`- or `F_2^N`-shift games, but only on hosts the KKMO
    reduction chooses. So nothing forbids this claim from using shift
    instances on DKKMS hosts, unless a BM-type algorithm is proved for those
    hosts.
  * **New prerequisite on the parameters (conditional).** The spectral gate
    (K1') of `akkstv-rounding-holds-on-all-loop-free-constraint-graphs` applies
    to *every* unique game on a loop-free host, not only to orientation lifts.
    Assume `folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes`
    (OPEN; gap `c(l)`, conjectured about `4^(-l)/2`). Then a reduction as in
    this claim on folded hosts must have `c(l) < X(delta) eta` on some YES
    outputs, unless P = NP. So `l` must grow as `eta -> 0`, with
    `l >= log_4(1/(2 X(delta) eta))` at the conjectured gap. The DKKMS choice
    of `l` as a function of the soundness alone cannot work at fixed `delta`.
    On unfolded hosts, the gap is `Theta(beta)`, and the same gate forces
    `beta <= X(delta) eta / C`. The lease e2-w2-ugc-h3 reported the plain
    Grassmann-edge-law version of this cap. It has not landed on this branch.
  * **Decomposition of the claim into prerequisites that can each fail.**
    - (a) The host's YES spectral gap is `o(eta)`. On folded DKKMS hosts this
      forces `l = l(eta)`, conditional as above.
    - (b) No BM-type Affine-UG algorithm exists on the host family, or the
      instances have non-cyclic holonomy.
    - (c) Soundness `delta` survives the `l`-growth that (a) requires. DKKMS
      soundness analysis fixes `l` from `delta`, so this is new.
