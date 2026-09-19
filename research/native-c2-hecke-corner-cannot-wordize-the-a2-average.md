---
rg: 2
id: native-c2-hecke-corner-cannot-wordize-the-a2-average
kind: claim
title: The native C2 Hecke corner cannot wordize the A2 two-path average
distinct_from:
  native-a2-two-path-average-is-not-an-ordinary-word-compression: That rules out a bare lamp-corner compression by one word; this tests the first internal finite-Hecke refinement and computes its support, trace, and section-covariance failures.
  finite-subgroup-hecke-literals-cannot-block-escape: That classifies when one finite-subgroup literal is a projection; this asks whether one explicit native finite corner produces a prescribed two-term transport average which is not itself a projection.
  sl3-one-over-forty-two-packet-is-external-or-folded: That rules out all exact finite sources of the required rank; this gives the sharper local double-coset and parahoric-covariance obstruction for the smallest candidate `K=C_2`.
---

Take the explicit order-two element

```text
c=diag(-1,-1,1) in D,
K=<c>,
q=(1+c)/2 in C[K].                                    (CHC1)
```

It is a particularly favorable candidate: for the A2 holonomy

```text
d=x_23(2) in D                                         (CHC2)
```

one has

```text
c d c^(-1)=d^(-1).                                    (CHC3)
```

Nevertheless it fails every required interface.

# Double-coset support cannot be the two A2 paths

For any group element `g`,

```text
qgq=(g+cg+gc+cgc)/4.                                  (CHC4)
```

Its group-basis support is the double coset `KgK`.  Since `|K|=2`, this
double coset has either two or four elements.

If it has four elements, every coefficient in `(CHC4)` is positive and no
two terms cancel or merge, so it cannot equal a two-path average.  If it has
two elements, then `g` normalizes `K` and

```text
KgK=gK={g,gc}.                                        (CHC5)
```

The relative word between its two support elements is an involution
conjugate to `c`.  But the desired arithmetic paths

```text
a=u d u^(-1)=b d,             b=x_13(2)                (CHC6)
```

have relative word `b^(-1)a=d`, of infinite order.  Hence no `g` gives

```text
qgq=(a+b)/2                                             (CHC7)
```

or the corresponding transported-corner version.  The inversion symmetry
`(CHC3)` does not help: it exchanges `d` and `d^(-1)` inside a four-term
double coset but cannot turn an involution packet into the one-sided average
`1+d`.

# Rank and section covariance both fail

The canonical trace of this corner is

```text
tau(q)=1/2,                                            (CHC8)
```

not the shell-atom trace `1/42`.  Refining it by another internal finite
character packet cannot repair the exact rank: every finite subgroup of
`SL_3(Z[1/2])` has order at most `24`, and
`sl3-one-over-forty-two-packet-is-external-or-folded` rules out trace
`1/42` in such a packet.

More decisively, `q` is not a valid base `D`-covariant atom.  From `(CHC3)`
and the canonical group basis,

```text
||dqd^(-1)-q||_2^2
 =||[q,d]||_2^2
 =||(cd-dc)/2||_2^2
 =1/2.                                                 (CHC9)
```

Thus the exact section correction `a=bd` moves the proposed atom by a fixed
amount.  The raw denominator-section estimate cannot identify the two
paths on this corner; it pays the constant covariance defect first.

Therefore the smallest internal finite-order Hecke mechanism does not
wordize the A2 average.  It either retains four Fourier paths, collapses to
two paths with finite relative holonomy, or violates the native section
covariance by the fixed floor `(CHC9)`.  The desired trace-zero unipotent
holonomy cannot be synthesized from this finite packet.

The trace obstruction closes the whole finite arithmetic class, not only
this `C_2`: `no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace`
uses the order-`24` bound to show that no projection in `C[K]`, for any
finite `K<D`, can have canonical trace `1/42` at all.
