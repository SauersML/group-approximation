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
* **Eigen-free list rounding on the label-extended walk**
  (`low-label-threshold-rank-reductions-cannot-prove-ugc`, 2026-09-17). Take
  greedy Gram--Schmidt on the columns of `((I + A_L)/2)^t`, then a grid and
  per-vertex argmax. It rounds every game of value `>= 1 - eps` to
  `0.84 - eps`, deterministically in time
  `poly(Z) exp(O(R log R))` with `R = rank_(1-800eps)(A_L)`. It dies on
  instances with `R = omega(log Z / log log Z)`, such as long-code or
  noisy-cube fibre compositions and SSE constraint graphs with many
  eigenvalues near 1. As an obstruction it forces every UGC reduction to have
  YES outputs of super-logarithmic label-extended threshold rank unless
  `P = NP`.
* **Refuter biography and the linear-loss kill** (e-ugc-pull-inverter,
  2026-09-18). This traces what a refuting algorithm `A` would have to do on each
  hard family, and kills one named class.
  (a) *The line.* `unique-games-np-hard-above-the-two-c-minus-one-line` argues
  that `Gap-UG[c, s]` is NP-hard for `s > 2c - 1`; it is OPEN, because its mixing
  proof has not been refereed, so everything in (a) below is conditional on it.
  Granting it: since `(1 - eps, eps)` lies below that line for `eps < 1/3`, `A`
  must decide a point in the open triangle
  `0 < s < 2c - 1`. Conversely, deciding any single point there already gives
  this claim; that converse is unconditional, being pure monotonicity. The class
  that would die: polynomial-time rounders, relaxation-based
  or not, with alphabet-uniform linear loss `val >= 1 - x => output >= 1 - Cx`
  and `C < 2`. They die at one fixed alphabet `k(C)`, at the decision step on
  KMS instances mixed with a satisfiable identity edge, where the completeness
  error is `x` and the soundness error is `2x`. The invariant is branch
  multiplicity `2`. Losses growing with `k` (CMM, Galois `O(eps log k)`),
  constants `>= 2`, and non-linear guarantees survive.
  (b) *2-to-2 Grassmann instances.* `A` cannot extend relation-generically to
  fan-out `2`, because `two-to-two-games-theorem` makes
  `Gap-2to2[1 - eps, eps]` NP-hard. So `A` must use uniqueness itself, not merely
  bounded fan-out, and every such use breaks when a constraint has two branches.
  (c) *Rich 2-to-1.* By `sd-rich-and-unique-games-sos-gaps-interconvert`, `A`
  composed with the noise test solves admissible-design rich 2-to-1 games, while
  general 2-to-1 games are NP-hard with imperfect completeness. So the
  interconversion must fail off the admissible designs, consistent with
  `affine-long-code-test-has-no-uniform-soundness`.
  (d) *Small-set expanders.* Composed with the polynomial-time reduction of
  `small-set-expansion-hypothesis-implies-ugc`, `A` decides the SSE gap problem,
  so `A` also refutes SSEH. On the image of that reduction, and on every UGC
  reduction's YES outputs, label-extended threshold rank is super-logarithmic
  (`low-label-threshold-rank-reductions-cannot-prove-ugc`), so `A` cannot be
  threshold-rank enumeration.
  (e) *SoS.* The known gaps (KV, short code, noisy cube) are refuted at constant
  degree (BBHKSZ). If `sos-cannot-refute-unique-games-at-completeness-one-half`
  were established, mixing would give SoS pseudo-gaps with error ratio `2`, and
  every SoS rounding with a linear loss constant below `2` would fail without the
  `P != NP` assumption.
  What would settle it: an NP-hardness reduction at any single point strictly
  below the line proves no UGC-refuting `A` exists unless `P = NP`. Affine-view
  verifiers over DKKMS inputs cannot supply it
  (`grassmann-composed-2to2-coarsenings-are-satisfiable`). This claim stays OPEN.
  Note that (a) and (e) rest on
  `unique-games-np-hard-above-the-two-c-minus-one-line`, which is itself OPEN
  pending a referee read of its mixing argument; (b), (c) and (d) do not.
