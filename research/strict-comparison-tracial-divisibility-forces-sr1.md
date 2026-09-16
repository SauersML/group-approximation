---
rg: 2
id: strict-comparison-tracial-divisibility-forces-sr1
kind: claim
title: For exact unital simple algebras with strict comparison, any form of Winter's tracial divisibility forces stable rank one
distinct_from:
  strict-comparison-rank-surjectivity-forces-sr1: that needs surjectivity of the rank map; this needs only order zero tracial divisibility with a lossy constant 1/(m+1), or Cuntz-semigroup m-almost divisibility.
  strict-comparison-property-tm-forces-sr1: that is the Fu-Lin theorem with property (TM) as hypothesis; this chains it with Fu's exact-case equivalences and matches the hypotheses, so that Winter's and STW's weaker divisibility forms suffice.
  strict-comparison-forces-tracially-divisible-unit: that asks whether strict comparison divides the single element 1_A; this assumes tracial divisibility of every positive contraction of every matrix algebra and concludes stable rank one.
  stw99-problem-xxviii-tracial-divisibility-gamma: that asks whether Winter's tracial divisibility gives uniform property Gamma, without any comparison hypothesis; this adds strict comparison and concludes stable rank one, not Gamma.
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be a unital, simple, separable, exact, non-elementary C*-algebra with
`T(A) ≠ ∅`. Assume strict comparison of positive elements against traces: for
`a, b ∈ M_∞(A)_+`, `a ≲ b` whenever `d_τ(a) < d_τ(b)` for every `τ ∈ T(A)`.
Suppose any one of the following holds:

- **(a)** `W(A)` is `m`-almost divisible for some `m ≥ 0` (Winter): for every
  positive contraction `a ∈ M_∞(A)` and `k ≥ 1` some `x ∈ W(A)` has
  `kx ≤ [a] ≤ (k+1)(m+1)x`;
- **(b)** `A` is tracially `m`-almost divisible for some `m ≥ 0` (Winter): for
  every positive contraction `a ∈ M_k(A)`, every `n` and `ε > 0` there is a
  c.p.c. order zero `φ: M_n → her(a)` with `τ(φ(1_n)) ≥ τ(a)/(m+1) − ε` for all
  normalized quasitraces `τ`;
- **(c)** the tracial divisibility property of STW Problem XXVIII, for positive
  contractions: as in (b) with `m = 0`, strict inequality, and `τ` ranging over
  `T(A)`;
- **(d)** any of the eight properties of
  `fu-exact-simple-tracial-regularity-equivalences`, including real rank zero
  of `l^∞(A)/J_A` and Property (TM).

Then `sr(A) = 1`. Consequently `Γ: Cu(A) → LAff_+(QT~(A))` is surjective, and
`A` is K1-bijective.
