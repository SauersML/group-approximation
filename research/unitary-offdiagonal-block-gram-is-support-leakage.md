---
rg: 2
id: unitary-offdiagonal-block-gram-is-support-leakage
kind: claim
title: The Gram defect of a unitary off-diagonal block is bounded by one support-leakage row
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that assumes a partial isometry and uses its swap to wordize arbitrary intertwining rows; this starts with an arbitrary unitary word and proves that one supported off-diagonal block is automatically an approximate partial isometry.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that gives the rank obstruction after a coarse-to-fine Gram row has been recovered; this reduces recovery of that Gram row to one carrier-support transport defect.
  controlled-swap-wordizes-matrix-corner-without-adjoint-dilution: that requires a nonlinear controlled copy swap for a prescribed projection; this needs only a unitary word and two already exactified carrier projections.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial matrix algebra, let
`e,f in M` be projections, and let `J in M` be unitary.  Put

```text
X=fJe,                    L=(1-f)Je.                    (UBL1)
```

Then exactly

```text
e-X^*X=L^*L,                                               (UBL2)

tau(e-X^*X)=||L||_2^2,
||e-X^*X||_2^2<=||L||_2^2.                              (UBL3)
```

Thus an authenticated off-diagonal block of a unitary word is automatically
an approximate source-full partial isometry as soon as its wrong-target
support leakage is small.  No separate polar decomposition, inverse block,
or `XX^*` relation is required.

There is a one-word form when the carrier reflections are themselves words.
Let

```text
R_e=1-2e,                    R_f=1-2f,
C=R_f J R_e J^*.                                         (UBL4)
```

Since

```text
(R_fJ-JR_e)e=2(1-f)Je,                                  (UBL5)
```

unitary invariance and `(UBL3)` give

```text
||e-X^*X||_2^2
 <=1/4 ||C-1||_2^2.                                    (UBL6)
```

Combining `(UBL6)` with the coarse-to-fine `M_2` versus `M_4` rank floor
from `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` yields the
particularly clean endpoint

```text
tr(P)<=||R_f J R_e J^*-1||_2^2.                        (UBL7)
```

Here both matrix-unit packets have common identity `P`, `e` is one coarse
diagonal corner, and `f` one fine diagonal corner.  Therefore the remaining
decoder does not have to prove that the three-root word is close to a
preselected partial-swap formula.  It only has to prove one supported
carrier-conjugacy row.

If packet exactification perturbs the named carrier reflections and the word
by `eta`, fixed-word telescoping adds only `O(eta)` to the right side of
`(UBL6)`.  The exact identity is dimension-free, so no rank- or ambient-size
constant enters that transfer.

