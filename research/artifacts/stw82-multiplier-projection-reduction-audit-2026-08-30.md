---
rg: 2
title: STW LXXXII multiplier-projection reduction audit (2026-08-30)
kind: artifact
---

# Result

The unital split-AF quotient case is equivalent to one sharply isolated
permanence question:

```text
dim_nuc(A+C p)=dim_nuc(A)
```

for every projection `p` in the multiplier algebra of an arbitrary
C*-algebra `A`.  It is already enough to prove the maximum formula for
unital split extensions with two-point quotient `C direct_sum C`.

# Algebraic checks

For a finite-dimensional quotient `direct_sum M_(r_j)`, compressing by the
sum of one lifted minimal projection per block is dimension-neutral.  A
finite matrix-unit frame embeds the original middle algebra as a corner of a
matrix algebra over the compression, while the compression is itself a
hereditary corner of the original algebra.  No separability, stability, or
abstract Morita-invariance theorem is needed.

The compressed quotient is `C^k`.  Its lifted coordinate projections may be
adjoined one at a time, and each is a multiplier of the algebra obtained at
the preceding step.  This proves that the one-projection assertion implies
the finite-dimensional assertion.  Dense finite-dimensional AF stages then
give the AF assertion by local permanence.

Conversely, unitizing `A+C p` produces a split two-point quotient unless
`p` or `1-p` already lies in `A`; those exceptional cases are respectively
trivial adjunction and ordinary unitization.  Nuclear dimension is invariant
under minimal unitization, so the two-point formula implies the
one-projection assertion.

There is also a positive noncentral case.  For sigma-unital `A`, if the
multiplier projection is full (`closure(ApA)=A`), then the assertion is
trivial when `p in A`; otherwise `p` is full in `A+C p` and its corner is
the unitization of `pAp`.  Strong Morita invariance and hereditary
monotonicity prove `dim_nuc(A+C p)=dim_nuc(A)`.  For a
nonfull projection, writing `L=closure(ApA)` computes the generated ideal
`L+C p`, but leaves residual quotient `A/L`; the missing comparison is once
again an extension-gluing problem.

# Exact boundary of the current proof

For the compressed ideal `J` and quotient lifts `e_1,...,e_k`, the lifted
stage centre commutes with `J` exactly when all off-diagonal Peirce corners
`e_j J e_l`, `j!=l`, vanish.  If one is nonzero, a norm-one element in that
corner has commutator norm one with `e_j`.  Thus the stage-centre direct-sum
argument has an exact, maximal obstruction.

This is a reduction and a proof-strategy no-go, not a proof or disproof of
multiplier-projection invariance.  A successful continuation must control
the nuclear dimension of `A+C p` without replacing `p` by a central block
projection or assuming the off-diagonal Peirce corners vanish.
