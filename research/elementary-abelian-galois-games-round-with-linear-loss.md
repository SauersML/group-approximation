---
rg: 2
id: elementary-abelian-galois-games-round-with-linear-loss
kind: claim
title: Galois unique games over F_p^N with SDP value 1-eps have a subgroup-complement labeling of value 1-O_p(eps log k), and this rate is tight
distinct_from:
  sd-rich-and-unique-games-sos-gaps-interconvert: that transfers SoS gaps between UG and admissible 2-to-1 games; this is a rounding theorem with linear loss for symmetric quotient instances over elementary abelian groups.
artifacts:
  - research/artifacts/ugc-galois-games-2026-09-12.md
---

**ESTABLISHED.** Let `G = F_p^N`, `K <= G` of order `k = p^r`, and `mu`
symmetric. Suppose `Gal(G,K,mu)` (see
`galois-unique-game-value-is-transversal-expansion`) has basic SDP value at
least `1 - epsilon`, or more generally admits a `K`-orthogonal positive-definite
certificate of value `1 - epsilon`. Then some subgroup complement `T` of `K`
gives

```text
val >= 1 - C_p epsilon log_p k,     C_p = 2p/((p-1)(1-cos(2 pi/p))),   C_2 = 3/2,
```

and `T` is found greedily in time polynomial in `|G| |supp mu|`, with no SDP
solve.

The mechanism is as follows. The certificate's character weights restrict to
the uniform measure on `Khat`. So more than a `1/p` fraction of `Khat` is the
restriction of characters with eigenvalue `>= 1 - 2p epsilon/(p-1)`, and these
restrictions contain a basis. The common kernel of `r` lifts is a complement of
`K`. By Markov, each lift costs at most `eta/(1-cos(2 pi/p))` in expansion.

**Sharpness.**

* *Linear rate attained.* On the Khot--Vishnoi instance
  (`F_2^N`, Hadamard `K`, `epsilon`-noise), `SDP >= 1 - 2 epsilon`. With
  `t = epsilon log_2 k`, Bonami--Beckner gives
  `(1-epsilon)^(log_2 k) <= val <= 2^(-t/(1-epsilon))`, so `1 - val = Theta(t)`
  for `t <= 1`.
* *Exponent hypothesis necessary.* `Gal(Z_(2n), {0,n}, unif{+-1})` is the
  `n`-cycle with odd holonomy. It has `val = 1 - 1/n` and certificate value
  `cos^2(pi/2n)`, so `1 - val >= (2/pi) sqrt(epsilon)` with `k = 2`: over cyclic
  groups the loss is square-root.

**Bearing on UGC.** Symmetric gap constructions over exponent-`p` groups can
separate SDP from integral value only when `epsilon log k -> infinity`. That is
the regime Charikar--Makarychev--Makarychev already force for all unique games,
and here the loss is linear rather than square-root. Quotient gap instances
cannot do better. This neither proves nor refutes `unique-games-conjecture`.
The novelty check was bounded; see the artifact, Section 7.

DERIVATION elementary-abelian-galois-games-round-with-linear-loss-proof
