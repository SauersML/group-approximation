---
rg: 2
id: unique-games-hard-on-non-sse-grassmann-constraint-graphs
kind: claim
title: Gap-UG[1 - eta, delta] is NP-hard already on unique games whose constraint graph is a Grassmann 2-to-1 constraint graph, which has small non-expanding zoom-in sets, so UGC could be proved without any small-set-expanding instance
distinct_from:
  small-set-expansion-hypothesis: that is hardness of expansion on SSE-type instances, equivalent to UG on SSE graphs; this asks for UG hardness exactly on graphs that are not small-set expanders.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that claim implies this one by taking the orientation lift, whose constraint graph is the source Grassmann graph; this one allows any unique constraints on that graph and needs no selector.
  grassmann-hosted-unique-games-cap-completeness: that is a proposed gate on this claim -- it asks whether this claim, restricted to the uniform (density one) Grassmann constraint graph, is equivalent to P = NP and caps the completeness any Grassmann-hosted reduction can reach; this is the request itself, and it stays open both inside the completeness window that gate would leave and through the density and biregularity escapes the gate does not cover.
  grassmann-graphs-have-constant-normalized-spectral-gap: that is the graph-theoretic question of whether the constraint graphs named here have spectral gap above (q-1)/q and expansion floor (1 - mu)(q-1)/q; this is a hardness request about unique games placed on them.
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

* **Global spectral gap of the host, not its small-set expansion
  (2026-09-18, swarm-0917, scale-shifter).** **Refuted by all three referee
  lenses at bullet 3 below; both new nodes were demoted to OPEN at landing.**
  The proposal was that this claim, read with the uniform DKKMS edge law, is
  equivalent to `P = NP`, and that the denial A3 rests on an equivocation. The
  first half survived review; the second was refuted, and it is the second that
  bears on A3. New nodes, both **OPEN**:
  `grassmann-graphs-have-constant-normalized-spectral-gap` and
  `grassmann-hosted-unique-games-cap-completeness`; their routes are kept as
  attempt artifacts
  `research/artifacts/grassmann-spectral-gap-recursion-proof-2026-09-18.md` and
  `research/artifacts/grassmann-completeness-cap-proof-2026-09-18.md`; replay
  `experiments/grassmann-spectral-gap-2026-09-17/check_grassmann_gap.py`
  (`ALL PASS`, exit 0). Verdicts `96bc7dfa`, `124cfa4b`, `17e004e3`, all
  `refuted`. The full referee reasons are recorded on
  `grassmann-hosted-unique-games-cap-completeness` and
  `grassmann-graphs-have-constant-normalized-spectral-gap`.

  1. *The invariant.* `lambda_2(Gr_q(n,l)) = [n]_q/(q [l]_q [n-l]_q) > (q-1)/q
     >= 1/2`, exactly, uniformly in `n`, `l` and in any alphabet placed on the
     graph. Proof: the down-up walk at level `l` and the up-down walk at level
     `l-1` are `D^*D` and `DD^*` for the same `D`, so they share their nonzero
     spectrum; reading both off gives
     `(1 - 1/[n-l+1]) lambda_2(l) = (1 - 1/[l]) lambda_2(l-1)`, which telescopes
     from the complete graph `Gr_q(n,1)`.
  2. *The step where the claim dies.* Bullet (K1) of
     `spectral-gap-ratio-reductions-cannot-prove-ugc` kills, at the **YES
     output and before any soundness analysis**, every reduction whose YES
     outputs are loop-free regular with `lambda_2 >= X(s)(1 - opt)`. Here
     `lambda_2 > 1/2` is fixed while this claim sends `1 - opt <= eta -> 0`. So
     for any fixed `delta` and any `eta < 1/(2 X(delta))` the reduction this
     claim asks for puts 3SAT in P. The converse also holds (a counting argument
     supplies a Grassmann-hosted unique game of value `<= delta`), so on that
     restriction the claim would be *equivalent* to `P = NP`, hence strictly
     stronger than `unique-games-conjecture` rather than a decomposition of it.
     All three referees checked this bullet by hand and found it sound; it is
     nevertheless carried as OPEN, because it lives on
     `grassmann-hosted-unique-games-cap-completeness`, which was demoted over
     bullet 3.
  3. *A3 --- **this bullet is what the referees refuted**, and it is why both
     new nodes are OPEN.* It asserted that the Grassmann graph *is* a small-set
     expander in the sense `small-set-expansion-hypothesis` and
     Raghavendra--Steurer use, on the ground that every set satisfies
     `Phi(S) >= (1 - mu(S)) lambda_2 > (1 - mu(S))(q-1)/q`, and that the zoom
     sets, being the equality cases, "carry no information beyond `lambda_2`".
     Both halves are false. `Gap-SSE` is a promise problem, and the sense those
     sources use is the **NO** side, near-perfect expansion
     `Phi_G(delta) >= 1 - eta` --- not "no small set has `Phi <= eta`". The
     numbers of this very attempt refute the substituted reading: the zoom-ins
     have `mu(Z_x) = [l]/[n] -> 0` with
     `Phi(Z_x) = q^(l-1)/[l] -> (q-1)/q < 1` (e.g. `mu = 9.5e-7`,
     `Phi = 0.500000` at `q=2, n=40, l=20`). So `Gr_q(n,l)` is neither a YES nor
     a NO instance of `Gap-SSE(eta, delta)` for `eta < 1/q`: it lies in the
     promise gap, and it is *not* a small-set expander as the literature means
     it. And equality in `Phi(S) >= (1 - mu)lambda_2` says only that
     `1_S - mu` lies in the second eigenspace; a Ramanujan graph with the same
     `lambda_2` has `Phi(S) = 1 - o(1)` at `mu(S) = o(1)`, so the extremal small
     sets carry strictly more than `lambda_2` --- high threshold rank, which is
     exactly the DKKMS/KMS structure the Bafna--Minzer line consumes.

     **Corrected reading.** A3's expansion premise is *correct* as standardly
     meant, and the KMS counter-signal "UGC may be true while SSEH is false" is
     untouched by anything in this attempt --- Theorem 4 confirms it. The
     premise is, however, **inert** for the kill in bullet 2: that kill runs on
     the global gap `lambda_2` alone and never consults the small-set profile.
     So this attempt does not deny A3; it shows that A3's premise, true or not,
     is not what stands between H3 and a proof. Whether H3 itself survives is
     the separate question in bullet 2, and the node carrying that question is
     itself OPEN.
  4. *What the kill would leave open even if restored.* Completeness
     `<= 1 - rho(q-1)/(q X(delta))`, where `rho`
     is the share of the edge law that is uniform on the Grassmann relation.
     `unique-games-hard-at-completeness-one-half` and `two-to-two-games-theorem`
     live safely below that ceiling, so the `1/2` wall in the attempt above is
     consistent with the ceiling but is not explained by it. The two escapes are
     stated exactly in `grassmann-hosted-unique-games-cap-completeness`:
     `rho -> 0` (an edge law concentrating off the uniform Grassmann relation,
     which is then not the DKKMS test), and non-regular hosts --- in particular
     the **bipartite containment host** on which an orientation lift actually
     runs, where (K1)'s survivor (S1) applies even though that host also has a
     constant gap (`> 1 - q^(-1/2)`). Extending (K1) past (S1) would kill
     `parity-leaking-branch-selectors-reach-near-perfect-completeness` by the
     same argument; that extension is posted as a need and is not claimed here.
