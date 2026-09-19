---
rg: 2
id: small-set-expansion-hypothesis
kind: claim
title: Small-Set Expansion Hypothesis -- for every eta there is delta making it NP-hard to tell Phi_G(delta) >= 1-eta from Phi_G(delta) <= eta
distinct_from:
  unique-games-conjecture: that is hardness for permutation-constraint games; this is hardness for approximating the edge expansion of sets of measure delta in a graph, which implies it (small-set-expansion-hypothesis-implies-ugc).
---

**OPEN.** Raghavendra--Steurer (STOC 2010), Conjecture 1.3. For a regular graph
`G`, put `Phi(S) = |E(S, V \ S)|/(d |S|)` and
`Phi_G(delta) = min_(mu(S) = delta) Phi(S)`. For irregular graphs, allow
`mu(S) in [delta, 10 delta]`. Then:

```text
for every eta > 0 there is delta > 0 such that Gap-Small-Set-Expansion(eta, delta),
distinguishing  Phi_G(delta) >= 1 - eta  from  Phi_G(delta) <= eta,  is NP-hard.
```

It implies `unique-games-conjecture` (route `ugc-from-small-set-expansion-hypothesis`).
It is equivalent to UGC restricted to instances whose constraint graph has
near-perfect expansion of sets of measure in `[delta, M delta]`
(Raghavendra--Steurer--Tulsiani, arXiv:1011.2586, Corollary 3.3). No converse
implication from UGC is known.

In this graph's Galois language (`galois-unique-game-value-is-transversal-expansion`),
a unique game with a Cayley lift is exactly small-set expansion of the lift at
density `1/k`, restricted to transversals.

## Attempts

* **Threshold rank (Arora--Barak--Steurer, FOCS 2010).** A graph with
  polynomially many eigenvalues near `1` contains a small non-expanding set,
  which yields subexponential-time algorithms for the gap problem. Where it
  stops: nothing at polynomial time. Barak--Gopalan--Hastad--Meka--Raghavendra--Steurer
  (arXiv:1111.0405, abstract, verified 2026-09-12) construct, for every
  `eps > 0`, an `n`-vertex graph where every set of `o(n)` vertices has
  expansion `1 - eps`, but more than `exp(log^delta n)` eigenvalues exceed
  `1 - eps`. That answers ABS's question, whose starting point was the noisy
  hypercube with `poly(log n)` such eigenvalues. So large threshold rank below
  that scale does not force a non-expanding small set. The ABS algorithm's
  running time was not re-read from the paper here (source not retrieved).
* **SoS-certified hypercontractivity.** By
  Barak--Brandao--Harrow--Kelner--Steurer--Zhou (arXiv:1205.4484v3, abstract,
  verified 2026-09-12), a graph is a small-set expander iff the projector onto
  its top eigenvectors has bounded `2 -> q` norm, and constant rounds of SoS
  certify this for the noisy cube and the short-code instances. Where it stops:
  a general graph has no low-degree hypercontractive certificate, and by item 1
  of that abstract, approximating the `2 -> q` norm well refutes SSEH.
* **Elementary abelian Cayley lifts.** For Cayley graphs of `F_p^N`, the linear
  rounding of `elementary-abelian-galois-games-round-with-linear-loss` turns an
  SDP certificate into a subgroup set of density `1/k` with expansion
  `O(eps log k)`. Where it stops: it applies only to transversal sets of Cayley
  lifts, and only when `eps log k` is small. In the SSEH regime,
  `eta log(1/delta)` is large, and the noisy cube shows that no contradiction
  arises there.
* **Khot--Minzer--Safra's informal counter-signal** (ECCC TR18-006,
  Appendix B, p. 55; [PDF], checked 2026-09-13).
  - The Raghavendra--Steurer reduction also maps `GapSSE[beta, 1-eps]` to
    `GapUG[~1/2, eps']` for an absolute constant `beta` ("say `beta = 3/4`").
  - The 2-to-2 proof reaches `GapUG[~1/2, eps']` without any reduction to Gap
    SSE. The graphs in that reduction "always have small non-expanding sets".
  - The authors present this as supporting the first author's suspicion that
    UGC may be true while SSEH is false.
  - This is an informal argument, not a theorem. It is not evidence against
    `ugc-from-small-set-expansion-hypothesis`, which remains a valid one-way
    route.
* **Gadget compositions over bounded-arity outer games (class kill, 2026-09-17).**
  `sticky-cylinder-gadget-compositions-cannot-prove-sseh` (ESTABLISHED) turns the
  RST remark (arXiv:1011.2586, p. 3) that gadget reductions "preserve ... lack of
  expansion" into a theorem, and it covers the KMS counter-signal above.
  - *Invariant.* The stickiness of the arity cylinders `X u N(X)` of the outer
    game.
  - *What survives the reduction.* Output graphs whose edges follow outer steps
    (fibred graphs) inherit sticky sets at every scale. This holds under walk
    powers, mixtures, parallel repetition and folding. So any projection outer
    game of left arity `k` with walk length `t` outputs graphs with
    `Phi(delta) <= 1 - k^(-ceil(t/2))` at every `delta` above the vertex-mass
    scale.
  - *Where it dies.* At the NO case of the output graph, for every
    `eta < k^(-ceil(t/2))`, before any soundness analysis.
  - *Survivors.*
    - (G1) Outer chains that are already pointwise small-set expanders. RST's
      H' gate is one; it consumes SSE hardness.
    - (G2) Output graphs that are not fibred.
    - (G3) Outer arity at least `eta^(-1/ceil(t/2))`, unbounded as `eta -> 0`.
  - Where it stops: it refutes no route that avoids fixed-arity outer
    composition.
* **Spread support overlap (class kill, 2026-09-17, wave 5).**
  `spread-support-overlap-forces-non-expanding-small-sets` (ESTABLISHED) removes
  the fibration and arity hypotheses of the previous bullet.
  - *Invariant.* The spread overlap profile. A support map `psi : V -> 2^U`
    has overlap `theta` if neighbours share a `theta` fraction of their supports.
    Its spread `rho` is the largest vertex fraction containing one atom.
  - *Theorem.* Some set of measure in `[delta, 10 delta]` has
    `1 - Phi >= theta - rho/delta`. The set is found by a p-biased zoom set
    `{v : psi(v) meets X}` at `E mu = 3 delta`, using concavity of `1 - (1-p)^s`
    and Efron--Stein.
  - *Where it dies.* At the NO case of the output graph, for `eta < theta - rho/delta`.
    - Grassmann-view graphs with codimension-one adjacency, the 2-to-2 test
      adjacency, die for `eta < 0.49` at every arity. This covers survivor (G3)
      over `F_2`.
    - Agreement tests die for `eta` below the intersection fraction.
    - Smooth `q`-query view graphs die for `eta < 1/q - rho/delta`, fibred or
      not. This covers the view-sharing part of (G2).
  - *Survivors.*
    - (H1) Dense-atom graphs, such as the noisy cube, where every high-overlap
      support map has an atom in at least a `delta (theta - eta)` fraction of
      vertices.
    - (H2) Graphs where neighbours share at most an `eta + rho/delta` fraction
      of every spread support.
  - Where it stops: the kill does not touch (H1) or (H2), and it proves nothing
    toward the hypothesis itself.
* **Two-sided threshold rank and certificates (attempted class kill, 2026-09-17,
  swarm-0917; refuted 2026-09-18, node back to OPEN).**
  `sse-reductions-need-high-threshold-rank-on-both-sides` is **OPEN**. Its
  spectral half (Theorems 1--3) was re-derived by three referee lenses with no
  failing step and its replay passes, but the gate's `(G-comb)` bullet imported
  the two combinatorial kills above with the wrong quantifiers, so the claim as
  stated does not hold. The attempt is kept at
  `research/artifacts/sse-two-sided-rank-gate-attempt-2026-09-17.md`. What
  follows is therefore an *attempt record*, not a kill in force.
  - *Invariant.* `rank_(1-800 eta)(A)` of the output graph and, on the NO side,
    the bit length of square certificates
    `c d s - e(x) = SOS + ideal(x_u^2 - x_u, sum x - s)` with `c < 1 - eta`.
  - *Step.* A non-expanding `s`-set `S` has `||(1_S)_lo||^2 <= s/100` on the
    eigenspaces of `(I + A)/2` below `1 - 50 eta`. Greedy Gram--Schmidt on the columns of `((I + A)/2)^t` captures
    the high part in dimension `2R`, and a grid thresholded at `1/2` recovers
    `T` with `(1 - Phi(T)) kappa(|T|) >= 0.49`.
  - *Why both sides.* A window lemma makes ACCEPT sound without any rank promise.
    So the "rank above `R*`" answer goes to whichever side carries the promise.
    The UG analogue `low-label-threshold-rank-reductions-cannot-prove-ugc` kills
    only the YES side.
  - *Where it dies.* In either case, `P = NP`, or `NP <= QP` for a polylog cutoff:
    - (K1) every YES output has threshold rank `O(log Z / log log Z)`;
    - (K2) every NO output has threshold rank `O(log Z / log log Z)`;
    - (K3) every NO output has a poly-bit square certificate, which gives `NP = coNP`.

    Under ETH with `Z <= n^A`, infinitely many YES outputs and infinitely many NO
    outputs have rank `> Z^alpha` for every `alpha < 1/A`.
  - *Gate (as proposed).* An SSEH reduction for `eta <= 1/800` on regular graphs
    would have to pass:
    - (G-spec) super-polylogarithmic threshold rank on both sides;
    - (G-cert) no poly-bit square certificates on NO outputs;
    - (G-comb) the unconditional spread-overlap and sticky-cylinder kills on NO
      outputs. **This is the refuted bullet.** At exact volume the spread-overlap
      kill needs `theta > 10 eta s/(s - 1) + rho/delta`, not `eta + rho/delta`
      (the `(s-1)/(10 s)` window factor is not removable), and the sticky-cylinder
      kill needs `eta + 2 varsigma'/delta < k^(-ceil(t/2))` and explicitly leaves
      outer arity `>= eta^(-1/ceil(t/2))` alive, so "bounded arity" is not its
      hypothesis. Restating (G-comb) with these quantifiers is the open repair.
  - *Survivors.* The BGHMRS graphs pass (G-spec) at their threshold, and their
    (G-cert) status was not settled. Abelian Cayley graphs pass (G-spec) only on
    the YES side: the hypercube has rank `2^(Omega(N)) = n^(Omega(1))` but is
    never a small-set expander, while the noisy hypercube is abelian Cayley with
    polylogarithmic threshold rank and so is exactly what (K2) would kill as a NO
    output.
  - Where it stops: the node is OPEN, the kills are conditional even once
    repaired, only regular exact-volume instances are covered, and the
    algorithmic `n^(O(D))` SoS form needs an SoS bit-complexity bound on the
    slice, which is not proved.
* **Subgroup dominance on `F_2^k` Cayley graphs (census and decomposition, 2026-09-17, swarm-0917).**
  Both results below were drafted as ESTABLISHED, but this lane's referee stage
  returned no verdicts, so both land **OPEN** with their proofs kept as attempts
  under `research/artifacts/`. No referee refuted either one; none read them.
  - *Census* (OPEN, `f2-cayley-sse-exact-census-small-k`; certified replay kept as
    an attempt, driver
    `experiments/sse-small-instances-2026-09-17/run_census.py`). It covers exact
    optima by branch and bound for `k <= 7`, with the admissibility of the
    pruning bound unaudited:
    - In all 39 noisy-cube cases, subcubes are exactly optimal.
    - The basic SDP (the Delsarte LP) overshoots by `0.004` to `0.015` at `s = 8`,
      and pure spectral certificates by `0.08` to `0.14`.
    - The only non-subgroup optimum found is `Cay(F_2^7, |a| <= 2)`, and there the
      SDP is exact.
  - *Theorem, claimed but unrefereed* (OPEN,
    `f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`; the proof is kept
    as an attempt).
    - *Statement.* Every `S` of measure `2^-c` in `F_2^k` has a law on subgroups
      `H` with `|H| = |S|` such that `Pr[a not in H] <= (E_c/2) d_S(a)` for
      all `a`, where `E_c <= c + 1.61`.
    - *Proof.* Sample characters from the spectral measure of `S` until they span
      dimension `c`. The subspace mass bound `mu(V) <= |V| 2^-c` bounds the
      stopping time, and Wald's identity gives the bound.
    - *Consequence.* For every weight law some subgroup has
      `Phi(H) <= (E_c/2) Phi(S)`, so subgroup enumeration decides
      `Gap-SSE(eta, 2^-c)` on `F_2^k` Cayley graphs in time `N^(c + O(1))`
      whenever `eta (c + 3.61) < 2`.
    - *Where it stops.* SSEH needs `delta <= 2^-(2/eta - 3.61)`, which is exactly
      the log-loss regime (the noisy cube again). So nothing is killed yet.
  - *Decomposition.* A new decomposition, whose prerequisite can fail:
    - `f2-cayley-subgroup-sets-are-constant-factor-optimal` (OPEN) asks that the
      subgroup-dominance constant satisfy `C* = sup C(S) < infinity`.
    - Route `f2-cayley-gap-sse-by-subgroup-enumeration` then gives
      `gap-sse-on-f2-cayley-graphs-is-polynomial`.
    - That would kill every SSEH reduction whose outputs are `F_2^k` Cayley
      graphs.
    - Contrapositive: an SSEH-hard `F_2^k` Cayley family forces `C* = infinity`.
      Some sets would then need to be `(1-eta)/eta`-far from every subgroup mixture.
    - *Evidence.* `C = 1` for `|S| = 4` and at `c = 1`, and `C` does not grow
      under products. The data maximum is `22/21`, including exhaustively at
      `(k, s) = (4, 8)`. Suggested attack: polynomial Freiman--Ruzsa applied to
      `A_theta = {a : d_S(a) <= theta}`.
  - Where it stops:
    - Neither result is refereed, so neither is established; treat both as
      drafted attempts until a referee pass survives.
    - Nothing is proved for general graphs.
    - The conjecture is open beyond size `4` and `c = 1`.
    - Cayley structure hidden behind an adjacency matrix is not addressed.
    - Groups other than `F_2^k` are not treated.
* **Label-extended lifts: value plus base profile (reframing, 2026-09-17).**
  `lifts-over-multiscale-expanders-expand-unless-ug-value-large` (ESTABLISHED,
  exact replay) splits the NO case of any reduction that outputs label-extended
  graphs `L(U)` of q-label games into two prerequisites. Every implication is
  proved.
  - *The prerequisites.* (N1) is soundness `val < nu^3 tau^2/64`. (N2) is base
    expansion `Phi_H >= 1 - nu/24` at every scale in `[1/q, tau]`.
  - *Sufficiency.* (N1) and (N2) imply `Phi_L(1/q) >= 1 - nu`, via a master
    inequality that truncates loads.
  - *Necessity.* `Phi_L(1/q) <= min(1 - val, Phi_H(1/q))`, witnessed by labeling
    sets and cylinders. So lifts give no scale gain, and twisting permutations
    over a sticky base stays inside the gadget-composition kill.
  - *Equivalence.* SSEH is equivalent to Gap-UG hardness on N2 bases. The
    converse direction cites RST Theorem 3.2's Gaussian profile.
  - Where it stops: this is a reframing, not progress on hardness. The open gap
    is between the necessary scale `{1/q}` and the sufficient range `[1/q, tau]`.
* **Gap-2->4 on the top eigenspace projector as an equivalent (dead end,
  2026-09-17).** The aim was SSEH iff a gap problem for `||P_(>=lambda)(L)||_(2->4)`
  at `delta = 1/q`.
  - *What holds.* A set with `mu = delta` and `Phi <= eta` gives
    `||P_(>=lambda)||_(2->4) >= sqrt((1-eta-lambda)/(1-lambda)) delta^(-1/4)`,
    by Hoelder on `P 1_S/sqrt(delta)`.
  - *Where it dies.* BBHKSZ (arXiv:1205.4484v3) Theorem 2.4 needs the NO norm to
    be `<= eps delta^(-1/4)` to certify expansion (item 1). Expansion only
    supplies `<= 2/sqrt(delta)` (item 2). Separately, RST's NO profile is
    vacuous for sets of measure below `gamma`, so it does not exclude large
    norms coming from tiny localized sets. No two-sided equivalence follows at
    either end.
* **Load rigidity on the YES side of lifts, and the base spectral gate
  (reframing, 2026-09-18, swarm-0917).** Two new claims. The lemma is
  **ESTABLISHED**; the gate was submitted as established and set back to
  **OPEN** after refereeing refuted its headline step (see the end of this
  entry).
  - *Lemma* (`lift-yes-sets-are-labelings-unless-the-base-loses-a-cut`, exact
    replay over 56,208 sets,
    `experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py`). For a
    regular base and `S <= V x [q]` of measure exactly `1/q` with
    `Phi_L(S) <= eta`, write `P = supp S`, `A_0 = V \ P`, `beta = mu(A_0)`.
    Then `a_uv <= l_u 1(v in P)` gives `E[l_u 1(v not in P)] <= eta`, hence
    `mu(A_0) Phi_H(A_0) <= eta`; integrality of the loads gives
    `Pr[l_u != l_v] <= 2 eta`; and the canonical labeling on `{l = 1}` has value
    `>= 1 - eta - 4 beta`. Spectral trichotomy: `val(U) >= 1 - 5 sqrt(eta)`, or
    `lambda_2(H) <= 4 sqrt(eta)`, or `mu(P) < sqrt(eta)/2`. So the necessity
    half of `lifts-over-multiscale-expanders-expand-unless-ug-value-large` is
    matched by a converse: up to `4 mu(A_0)` the only non-expanding sets of a
    lift at density `1/q` are labeling sets and base sets.
  - *Gate* (`sseh-lift-routes-need-spectrally-defective-bases`, **OPEN**,
    conditional on `P != NP`, attempted route
    `sseh-lift-base-spectral-gate-proof`). The part that refereeing confirmed:
    the lemma supplies the near-satisfying YES instance that the established UG
    gate `spectral-gap-ratio-reductions-cannot-prove-ugc` (K1) needs, and the NO
    side supplies soundness `eta` through the cylinder and labeling necessity;
    hence for a **support-spread** lift reduction
    `L n {lambda_2(H) >= 5 X(eta) sqrt(eta)}` is in `P`, so unless `P = NP` the
    hard core has `lambda_2(H) < 5 X(eta) sqrt(eta)` on **both** sides. The part
    that was refuted: the submission went on to conclude that the base's
    sparsest cut lies at measure `> tau` or `<= nu delta/6`, never inside the
    small-set window. That does not follow from `Phi_H(1/q) >= 1 - eta` and
    Cheeger, which give only `mu(B) != 1/q`. Excluding the window needs the
    multiscale profile `Phi_H(A) >= 1 - nu/24` on all of `[1/q, tau]`, and the
    necessity half of
    `lifts-over-multiscale-expanders-expand-unless-ug-value-large` forces N2
    only **at scale `1/q`** — it is a hypothesis of that claim's sufficiency
    half. So the profile jump is an added hypothesis on the NO bases, not
    something the reduction is forced to supply. The missing propagation is
    recorded as `single-density-expansion-forces-the-multiscale-profile`
    (**OPEN**, with a counterexample sketch against it: weakly coupled clusters
    of measure `rho` in `(1/q, tau]` expand at density `1/q` yet cut cheaply at
    `rho`).
  - *Galois form.* For `Gal(F_2^N, K, mu)` the gate says the almost-invariant
    character of the output Cayley graph can be taken trivial on `K`: the
    measure-`1/2` hyperplane of expansion `O(sqrt(eta))` contains the fibre
    subgroup. (K4) of the UG gate gives only that some character is
    almost-invariant.
  - *Decomposition of SSEH along lifts.* (P1) Gap-UG(`1-eps`, `nu^3 tau^2/64`)
    hardness on bases with the N2 profile, which implies SSEH. (P2) unless
    `P = NP`, some YES output of such a family has `lambda_2 = O(eps)`, and by
    the gate `lambda_2 = O(sqrt(eta))` on the hard core of both sides of a
    support-spread lift reduction; so (P2) is a shape constraint that cannot be
    discharged. (P3) no scale gain, so the `delta` quantifier of SSEH must be met
    by the base family and not by lifting; this one is established. (P4) the
    profile jump, which holds for families that carry N2 — since (P1)
    hypothesizes N2 this is not a restriction inside the decomposition, but it is
    also not forced on an arbitrary lift reduction, which is where the
    submission overreached. Each of (P1), (P2), (P4) fails without the others:
    identity permutations on a noisy cube satisfy (P2) and (P4) and fail (P1); a
    random game on a Ramanujan base satisfies (P1)'s soundness and fails (P2);
    `q` disjoint copies fail the profile at `1/q`.
  - Where it stops: the gate needs regular loop-free bases and the
    support-spread hypothesis; it is silent on reductions whose YES witness lies
    over a base set of measure `< sqrt(eta)/2` (then the witness is an
    approximate block system of size `> 2/sqrt(eta)`, and for `delta < 2 eta` —
    the regime SSEH needs — that branch survives); it is silent on outputs that
    are not label-extended graphs; and the rounding item is vacuous in the
    weighted `[delta, 10 delta]` window, where an `m`-fold labeling set is a
    genuine counterexample to it. Nothing here is evidence for or against the
    hypothesis.
  - *Referee outcome, 2026-09-18.* Three lenses replayed
    `check_load_rigidity.py` (56,208 sets, 0 failures) and re-derived the lemma
    step by step; all three accepted the lemma and the two-sided spectral gate.
    Two refuted the submitted claim at the profile-jump step above, and the
    third asked for the same wording fix. The gate claim was therefore set back
    to OPEN with the refutation and the repair recorded in its `## Attempts`;
    the lemma stands.
