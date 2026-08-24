---
rg: 2
id: rank-deficient-return-row-has-operator-norm-one
kind: claim
title: A rank-decreasing return row has operator norm exactly one, with no density hypothesis
distinct_from:
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that is the normalized-HS form of the same rank count, and its floor `tr(P)(1/r-1/s)` is proportional to the carrier density, so it says nothing on a carrier of vanishing trace; this is the operator-norm form, whose floor is exactly `1` on every nonzero carrier and never degrades.
  unitary-offdiagonal-block-gram-is-support-leakage: that bounds the Gram defect ABOVE by the support-leakage row, in the 2-norm, and is the reduction used to shrink a decoder target; this bounds the same row BELOW by 1, in the operator norm, and is the contradiction the decoder is aimed at.
  rectangular-wedderburn-block-isometry-gap: that compares unequal irreducible Fourier corners inside a regular finite-group chart and pays a Wedderburn block constant; this needs no chart, no group, and no representation theory -- only two projections of unequal rank and one unitary.
  low-gap-witness-spike-or-balanced-cut: that clips an operator-norm witness to isolate a vanishing-rank obstruction inside an optimization; this is the closed-form value of one fixed off-diagonal row and involves no clipping and no witness selection.
---

**ESTABLISHED.**  Let `H` be a nonzero finite-dimensional Hilbert space, let
`e,f` be orthogonal projections on `H`, and let `J` be any unitary.  Put

```text
X=fJe,                    L=(1-f)Je.                     (ROW1)
```

Then always

```text
X^*X+L^*L=eJ^*Je=e,       i.e.  e-X^*X=L^*L,             (ROW2)
```

and if moreover

```text
rank(e)>rank(f),                                          (ROW3)
```

then exactly

```text
||L||_op=||(1-f)Je||_op=1,
||e-X^*X||_op=1.                                          (ROW4)
```

No trace, no normalized rank, no lower bound on `rank(e)-rank(f)` beyond
`1`, and no bound on the ambient dimension enter.  `(ROW4)` is also
**amplification-blind**: replacing `(H,e,f,J)` by
`(H tensor K, e tensor 1, f tensor 1, J tensor 1)` multiplies both ranks by
`dim K` and leaves both values at `1`.

## The binary Leavitt specialization

Let `P` be a nonzero projection carrying two exact systems of matrix units

```text
(e_ij)_(i,j<=r),          (f_ab)_(a,b<=s),      r<s,      (ROW5)
```

with the same identity `P`.  Then `rank(e_11)=rank(P)/r` and
`rank(f_11)=rank(P)/s`, so `rank(P)` is a positive multiple of `s` and

```text
rank(e_11)-rank(f_11)=rank(P)(1/r-1/s)>=1.                (ROW6)
```

Hence for the first binary Leavitt refinement `r=2`, `s=4` and **every**
unitary `J`,

```text
||(1-f_11)J e_11||_op=1.                                  (ROW7)
```

Consequently any dimension-independent estimate of the form

```text
||(1-f_11)J(U)e_11||_op<=omega(Def_R(U)),   omega(t)->0,  (ROW8)
```

for a fixed return word `J` is contradictory as soon as the relator defect
is small enough.  This is the whole analytic content of the operator-norm
non-MF endpoint `authenticated-coarse-fine-return-forces-mf-collapse`.

## What this does and does not buy

It **removes the positive-density obligation**.  The normalized-HS floor
`(CFI2)` of `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` is
`tr(P)(1/r-1/s)` and therefore vanishes with the carrier density; the
operator-norm floor is `1` on a carrier of rank `s`.  Everything the program
currently spends on recovering a positive-density active core -- the
normal-generator reblocking of
`torsion-normal-generator-has-full-support-corona-core`, the paired mass
ledger of `paired-same-reservoir-boundary-lemma`, the `1/36` and `s_4`
constants -- is unnecessary for an operator-norm decoder.

It does **not** shrink the authentication problem, and the exact case shows
why.  If both packets are exact on a common nonzero `P`, `(ROW4)` says no
unitary whatsoever satisfies `(ROW8)`; there is no model to exhibit and no
near-miss to measure.  The entire difficulty therefore sits in recovering a
**common** carrier `P` from the presentation, which is
`opnorm-leavitt-coarse-fine-return-row`.  Nor may the row be imported from
the existing 2-norm calculus: see
`opnorm-return-row-cannot-come-from-an-hs-ledger`.
