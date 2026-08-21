---
rg: 2
id: forty-one-word-native-carrier-transport-certificate
kind: claim
title: Forty-one fixed word placements suffice to trigger the D8 recovery floor
artifacts:
  - experiments/atlas_transported_corner_overlap.py
  - experiments/atlas-transported-corner-overlap.json
distinct_from:
  separate-native-quarter-carrier-recovery: that asks for algebra membership of the two quarter projections; this reduces it to a finite support-word audit with an explicit threshold.
  finite-window-decoder: that recovers the finite paired-radical endomorphisms; this transports only the fixed support of two already constructed Hecke projections.
---

Write the two native atlas quarter carriers in reduced rational group-algebra
form:

```text
F=sum_(j=1)^37 c_j f_j,
G=sum_(k=1)^4  d_k g_k.                                (FWT1)
```

Exact Leavitt-prefix reduction gives

```text
sum_j |c_j|=11/4,
sum_k |d_k|=1.                                         (FWT2)
```

Let `A,B` be commuting linear subalgebras of a finite matrix algebra.  If for
every support word there are `a_j in A`, `b_k in B` with

```text
||f_j(U)-a_j||_2 <= eta,
||g_k(U)-b_k||_2 <= eta,                               (FWT3)
```

then linearity and the triangle inequality give

```text
dist_2(F(U),A) <= (11/4) eta,
dist_2(G(U),B) <= eta.                                 (FWT4)
```

The separate-carrier D8 theorem therefore implies

```text
(15/4) eta >= 1/8,
eta >= 1/30.                                           (FWT5)
```

Thus no finite-dimensional canonical microstate can transport all 41 support
words into the two commuting descendants with wordwise error `o(1)`.  It is
unnecessary to decode a whole coefficient algebra, construct a common PVM,
or promote either projection reflection to a group word.

More generally, if support word `w` has an individual transport error
`eta_w`, the exact certificate is

```text
sum_j |c_j| eta_(f_j)+sum_k |d_k| eta_(g_k) >= 1/8.    (FWT6)
```

This weighted form is the right interface for a van Kampen/relator audit:
each support word may have its own bounded derivation area.  Because the
support is fixed and finite, any finite areas give one positive
dimension-independent threshold.

The support sizes and coefficient masses are replayed with exact rational
prefix arithmetic on MSI.  No floating-point approximation is used.
