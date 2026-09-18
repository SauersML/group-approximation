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
