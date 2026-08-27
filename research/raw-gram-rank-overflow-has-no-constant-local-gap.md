---
rg: 2
id: raw-gram-rank-overflow-has-no-constant-local-gap
kind: claim
title: Raw operator-space Gram overflow has no dimension-free bounded-local-test gap
distinct_from:
  same-model-supercritical-clifford-trigger: that asks a constant-sound group compiler to activate an algebraically rigid Clifford system beyond the current model capacity; this shows that bare linear dependence of too many operator vectors does not itself provide such constant soundness.
  two-generator-amitsur-levitzki-dimension-oracle: that detects exact matrix degree through a growing polynomial identity; this gives a geometric family in which global rank failure is invisible to every bounded Gram window.
  word-recursion-cannot-amplify-sublinear-summands: that is a direct-sum dilution theorem; this obstruction occurs on one full carrier and comes from the vanishing local curvature of high-dimensional rank dependence.
artifacts:
  - research/artifacts/adversarial-error-delocalization-second-pass-2026-08-21.md
---

For every `r>=1` there are `r+1` unit vectors

```text
v_1,...,v_(r+1) in C^r
```

whose Gram matrix has rank `r` and satisfies

```text
<v_i,v_i>=1,
<v_i,v_j>=-1/r                 (i!=j).                 (RGO1)
```

Consequently every Gram submatrix on at most `k` named vectors differs from
the `k` by `k` identity by operator norm at most `(k-1)/r`.  In particular,
for each fixed query bound `k`, all bounded continuous predicates of at most
`k` pairwise inner products converge to their value on an orthonormal family,
although the whole `r+1` tuple is linearly dependent.

Therefore the capacity statement

```text
more than dim(V) vectors in V are linearly dependent
```

has no dimension-free soundness gap when tested only through a bounded menu
of raw Gram entries or bounded-size Gram minors.  Applied to conjugates of a
marked unitary in `L^2_0(M_d)`, the inequality `N>d^2-1` cannot by itself
replace the constant-gap Clifford/PCP backend: a bounded-local Gram tester may
see error only `O(1/d^2)`.

This does not rule out a genuine PCP of a **global** rank computation.  Such a
compiler must encode and robustly verify the growing linear-algebra
calculation; it cannot cite rank overflow itself as the constant-gap local
test.  Direct Gram determinants, sequential orthogonalization, and Schur
complements still face growing degree, conditioning, address-consistency, and
runtime-return costs.

