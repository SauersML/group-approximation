---
rg: 2
id: rank-density-and-small-joins-give-all-ranks
kind: claim
title: Rank density plus uniformly small Cuntz joins below every target gives all ranks, with no stable rank or comparison hypothesis
distinct_from:
  thiel-stable-rank-one-ranks-close-purity-with-comparison: that realizes all ranks under stable rank one, through (O6+), weak cancellation and functional infima; this isolates the one order-theoretic input that final step needs, upward directedness of the sets L'_f, and replaces the earlier steps by rank density.
  rank-density-and-strict-comparison-give-purity: that turns rank density and strict comparison into purity; this turns rank density and small joins into exact realization of every rank, and derives small joins from strict comparison as a corollary.
  all-ranks-occur-iff-continuous-ranks-are-dense: that is an exact equivalence via continuous ranks; this is a sufficient condition via maximal soft suprema, testable on algebras where continuity is hard to see.
---

Let `A` be unital, simple, separable and stably finite, with `S = Cu(A)`,
`u = [1]` and `K = QT(A)`. For `a in S` write `d(a)` for its rank function.
For `f in LAff(K)_(++)` put

```text
L'_f = { a' in S : a' << a for some a in S with d(a) << f in LAff(K) }.
```

- **(RD) Rank density.** For every strictly positive continuous affine `g` and
  every `eta > 0`, some `a in S` has `|d(a) - g| < eta` on `K`.
- **(SJ) Small joins.** For every `f in LAff(K)_(++)`, the set `L'_f` is upward
  directed. Concretely, if `d(a), d(b) << f`, `a' << a` and `b' << b`, there is
  `c` with `d(c) << f` and `c' << c` such that `a', b' <= c'`.

**Theorem.** (RD) and (SJ) imply that all ranks occur. More precisely,
`alpha(f) = sup L'_f` exists and `d(alpha(f)) = f` for every
`f in LAff(K)_(++)`.

**Corollary.** (RD) plus strict comparison of positive elements gives (SJ),
hence all ranks occur. The argument is direct and does not pass through purity,
Lin's stable rank theorem or Thiel's theorem.

**Where each hypothesis is spent.**
- (RD) supplies approximants way below `f` from beneath.
- (SJ) collects them under one supremum whose rank never exceeds `f`.
- In Thiel's stable-rank-one proof (arXiv:1711.04721, section `sec:rankCu`),
  (SJ) is the lemma proved from (O6+), functional infima and weak cancellation.
- No Edwards condition, (O6+), weak cancellation or stable rank hypothesis is
  needed once (SJ) is assumed.

**Boundary of the cell.**
- Every unital simple AH algebra has (RD) (`ah-algebras-realize-ranks-approximately`).
  So on AH algebras the Rank Problem follows from (SJ).
- Toms's no-Gamma AH algebra has (RD) and provably fails (SJ)
  (`toms-schubert-algebra-has-no-small-joins`).
- So (SJ) is not automatic in simple nuclear algebras. Any realization of all
  ranks there must use realizers that are not maximal soft suprema.

**Model test.** In `C([0,1])`, which is not simple, (SJ) holds for
`f = 1/2 + id`, but (RD) fails for traces at points: ranks are integers there.
So (RD) is load-bearing. Toms's algebra shows (SJ) is load-bearing.

Proof: `rank-density-and-small-joins-give-all-ranks-proof`.
