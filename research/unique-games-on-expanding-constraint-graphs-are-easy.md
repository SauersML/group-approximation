---
rg: 2
id: unique-games-on-expanding-constraint-graphs-are-easy
kind: claim
title: A deterministic polynomial-time SDP rounding finds a labeling of value 1 - O((eta/lambda) log(lambda/eta)) on every unique game of SDP value 1-eta whose regular constraint graph has normalized spectral gap lambda (AKKSTV 2008)
distinct_from:
  unique-games-gap-admits-polynomial-time-algorithm: that is the open algorithmic negation of UGC on all instances; this is the proved algorithm under the promise lambda_2 >> eta on the constraint graph.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that rounds games whose label-extended walk has few eigenvalues near 1; this needs only one spectral gap of the constraint graph, which is unrelated to the label-extended rank.
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that solves affine games on hypercontractive graphs through SoS; this solves arbitrary permutation games on spectral expanders through the basic SDP, independently of the alphabet size.
---

**ESTABLISHED, BY CITATION.** Arora, Khot, Kolla, Steurer, Tulsiani and
Vishnoi, *Unique Games on Expanding Constraint Graphs are Easy*, STOC 2008.
Theorem 2.4 of that paper: "There is a polynomial time algorithm that computes
a labeling Λ with val(Λ) ≥ 1 − O((η/λ) log(λ/η)) if the optimal value of the
SDP in Figure 1 for U is 1 − η". Here `λ = λ_2(G)` is the second smallest
eigenvalue of the normalized Laplacian of the constraint graph. The rounding is
derandomized by trying all `nk` choices.

The form used in this graph is as follows. There are an absolute constant
`C_A >= 1` and a deterministic polynomial-time algorithm `AKKSTV` with this
property. Let `U` be a unique game with a weighted-regular constraint graph
(the proof quoted in the citation route analyses regular graphs), with
`λ = λ_2(G) > 0`, and with `opt(U) >= 1 − η`, where `λ >= e η`. Then
`AKKSTV(U)` is a labeling of value at least `1 − C_A (η/λ) log(λ/η)`.

The bound does not depend on the alphabet size `k`. The same paper shows that
the factor is tight up to a constant under UGC (Theorem 2.6), and that for
`Γ-MAX2LIN` games `λ` may be replaced by the level-`r` Lasserre-style
Sparsest-Cut relaxation `z_r(G)` in time `(kn)^(O(r))` (Theorem 3.2). Credit is
the authors'; nothing is reproved here.

DERIVATION unique-games-on-expanding-constraint-graphs-are-easy-citation
