---
rg: 2
id: iwahori-local-global-defect-question
kind: claim
title: Local Iwahori defect controls global distance to a compatible representation
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
  - notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md
distinct_from:
  iwahori-outlier-repair: that is this repository's proposed sufficient condition -- a full-rank repair theorem in the one sector its own analysis leaves open; this is the published question in Dogon-Vigdorovich's own local-defect/global-defect form, which the repair theorem is an attack on.
  iwahori-fractional-transport-integralization: that is one intermediate step of the attack, converting a fractional transport plan into orthogonal blocks; this is the whole question the attack is aimed at.
  iwahori-nielsen-extension-transversality: that asks for transversality of the two opposite modular extension loci, one ingredient of the attack; this is the global modulus question the attack is aimed at.
  iwahori-nielsen-hs-bilipschitz: that is a dimension-free bi-Lipschitz estimate for one fixed Nielsen involution on the coordinates of Z*C_2 representations; this is the existence of a global modulus relating local Iwahori defect to distance to the compatible subvariety, over the whole representation variety of the free product of two copies of SL_2(Z).
---

**Dogon--Vigdorovich, arXiv:2506.20843v2, Question 1.2** (`problem!` in the
source), stated in their notation.

Let `Lambda = SL_2(Z) * SL_2(Z)` and let `X_FD(Lambda)` be the representation
variety of all finite dimensional unitary representations, with
`d_2(pi, pi') = max_(s in S) d_2(pi(s), pi'(s))` for a fixed finite generating
set.  Let `B_+`, `B_-` be the upper and lower Iwahori subgroups of `SL_2(Z)`
(pullbacks of the upper and lower triangular subgroups of `SL_2(F_2)`, each of
index three), and let `sigma : B_+ -> B_-` be the isomorphism implemented by
conjugation by `t = diag(sqrt 2, 1/sqrt 2)`, an element of the commensurator
but not the normalizer of `SL_2(Z)` in `SL_2(R)`.

Call `pi in X_FD(Lambda)` **compatible** if its two restrictions satisfy
`pi_+|_(B_+) = pi_-|_(B_-) o sigma`; compatible representations form a
subvariety identified with `X_FD(SL_2(Z[1/2]))`.  With
`S_+ = {[[1,0],[2,1]], [[1,1],[0,1]], -I}` a generating set of `B_+`, define

```text
def(pi) = max_(s in S_+) d_2(pi_+(s), pi_-(sigma(s))),
D(pi)   = inf { d_2(pi, pi~) : pi~ in X_FD(Lambda) compatible }.
```

One always has `def(pi) <= 2 D(pi)`.  The claim is the converse modulus:

> There is `f : R_+ -> R_+` with `lim_(x->0) f(x) = 0` such that
> `D(pi) <= f(def(pi))` for every `pi in X_FD(Lambda)`.

Equivalently, by the congruence subgroup property of `SL_2(Z[1/2])`:
representations of `SL_2(Z)` that almost factor through a congruence quotient
`SL_2(Z/n)` with `n` odd are close to ones that genuinely do.

By `dv-s-arithmetic-hs-stable-nonhyperlinear-extension` and their
Corollary 1.3, a positive answer yields a non-hyperlinear finite central
extension of `SL_2(Z[1/2])`.

## Transcription note

The source also asserts, in **commented-out** text, that this question is
equivalent to Hilbert--Schmidt stability of `SL_2(Z[1/p])` and that `SL_2(Z)`
is Hilbert--Schmidt stable.  Those sentences are not printed in v2 and are not
used here.  Only the printed implication (positive answer implies a
non-hyperlinear group, their Corollary 1.3) is consumed.

## Attempts

- **Full-rank outlier repair.**  This repository's line of attack, recorded at
  `iwahori-outlier-repair` and fed by `iwahori-outlier-localization` and
  `edge-pair-mixed-gap-collapse`.  Its residual obstruction is physical rank,
  not Hilbert-space dimension: an `o(d^2)` low-energy operator space can still
  contain an invertible matrix, the scalar line being the example.
- **Spectral sparsity alone.**  Refuted for that reason; see the same node.
- **Bounded branching.**  Index-three restriction/induction has uniformly
  bounded branching (`notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`)
  and this does not stop the identity's mass spreading over growing many
  cross-pairs.  Recorded negative.
- **Refutation by character rigidity is unavailable.**  By
  `character-rigidity-equals-hyperfinite-hs-stability`, stability implies
  character rigidity, so a failure of character rigidity would refute the
  question -- but `SL_2(Z[1/2])` is already known to be character rigid
  (Peterson--Thom), so that route is closed in advance.  The cheap negative
  answer does not exist.
- **Not attempted here: the negative side.**  No construction in this
  repository produces a sequence with `def(pi_n) -> 0` and `D(pi_n)` bounded
  below.  A negative answer would kill this route without touching the goal.
