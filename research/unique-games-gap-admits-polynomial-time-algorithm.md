---
rg: 2
id: unique-games-gap-admits-polynomial-time-algorithm
kind: claim
title: Refutation form of UGC -- for some eps > 0 a polynomial-time algorithm separates unique games of value >= 1-eps from value <= eps at every alphabet size
distinct_from:
  unique-games-conjecture: that is the NP-hardness conjecture; this is its algorithmic negation, which refutes it unless P = NP.
  sd-rich-and-unique-games-sos-gaps-interconvert: that transfers algorithms and gaps between UG and admissible 2-to-1 games; this is the target an algorithm for either would reach.
---

**OPEN.** There are `eps > 0` and a polynomial-time algorithm which, for every
alphabet size `k`, given a unique game `U` with `val(U) >= 1 - eps` or
`val(U) <= eps`, decides which. Unless `P = NP`, this refutes
`unique-games-conjecture`. It is the form in which a refutation would land as an
established negation.

**Constraints any such algorithm must respect.**

* It must fail at completeness `1/2`: `unique-games-hard-at-completeness-one-half`.
  So it must use completeness near `1`, not only soundness.
* On admissible-design rich 2-to-1 games it is the same problem
  (`sd-rich-and-unique-games-sos-gaps-interconvert`).
* It cannot be based on threshold rank alone at polynomial time: there are
  small-set expanders with more than `exp(log^delta n)` eigenvalues above
  `1 - eps` (Barak--Gopalan--Hastad--Meka--Raghavendra--Steurer, recorded in
  `small-set-expansion-hypothesis`).

## Attempts

* **Basic SDP rounding (Charikar--Makarychev--Makarychev 2006).** It gives
  value `1 - O(sqrt(eps log k))`, not re-read from the source here. It dies
  because UGC lets `k` grow with `1/eps`; Khot--Vishnoi gap instances need
  `eps log k -> infinity`, and on symmetric quotients that threshold is exact
  (`elementary-abelian-galois-games-round-with-linear-loss`).
* **Graph-restricted SoS algorithms.** Affine UG is easy on certifiably
  hypercontractive graphs (`affine-ug-easy-on-certifiably-hypercontractive-graphs`)
  and, at any constant completeness, on globally hypercontractive graphs such as
  Johnson, Grassmann and HDX walks
  (`affine-ug-easy-on-globally-hypercontractive-graphs`). They die on general
  instances. KKMO's reduction to affine UG does not preserve the constraint
  graph, and reductions can use graphs whose non-expanding sets have no succinct
  characterization.
* **Subexponential time (Arora--Barak--Steurer 2010).** It dies at
  polynomial time. As a consistency check, any NP-hardness reduction for UGC
  must blow instances up by a factor whose exponent grows with `1/eps`;
  otherwise ABS plus the reduction would give 3SAT in time `exp(n^(o(1)))`,
  against ETH. The exact ABS exponent was not re-read here.
* **Constant-degree SoS on known gap instances**
  (Barak--Brandao--Harrow--Kelner--Steurer--Zhou, arXiv:1205.4484v3, abstract
  item 2, verified 2026-09-12). "Constant rounds" of SoS certify the
  unsatisfiability of the noisy-cube and short-code instances. Item 1 of the
  same abstract: a graph is a small-set expander iff the projector onto its top
  eigenvectors has bounded `2 -> q` norm. It dies because it is
  instance-specific; no general SoS rounding at constant degree is known.
* **Symmetric (Galois) instances.**
  `galois-games-round-through-free-subgroups` rounds every Cayley-lift instance
  through free subgroups. It dies because hardness reductions do not output
  Cayley lifts.
