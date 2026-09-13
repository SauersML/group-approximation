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
* **SoS-certified hypercontractivity.** Degree-8 SoS certifies the
  small-set expansion of the noisy cube and of the short-code instances
  (Barak--Brandao--Harrow--Kelner--Steurer--Zhou, arXiv:1205.4484). Where it
  stops: it needs a low-degree hypercontractive certificate, which is not
  available for general graphs, and certifying `2 -> 4` norms is itself
  SSE-hard in general.
* **Elementary abelian Cayley lifts.** For Cayley graphs of `F_p^N`, the linear
  rounding of `elementary-abelian-galois-games-round-with-linear-loss` turns an
  SDP certificate into a subgroup set of density `1/k` with expansion
  `O(eps log k)`. Where it stops: it applies only to transversal sets of Cayley
  lifts, and only when `eps log k` is small. In the SSEH regime,
  `eta log(1/delta)` is large, and the noisy cube shows that no contradiction
  arises there.
