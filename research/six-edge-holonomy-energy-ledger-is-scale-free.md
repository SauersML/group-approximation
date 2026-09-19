---
rg: 2
id: six-edge-holonomy-energy-ledger-is-scale-free
kind: claim
title: The six-edge A2 holonomy has a dimension-free carrier-energy ledger
distinct_from:
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that identifies the literal holonomy and closes one fixed finite Chevalley packet; this is the scale-free normalized-HS inequality for arbitrary supported transition operators.
  adjacent-a2-chambers-share-only-commuting-wall: that shows every single wall admits a multiplicity rotation; this proves a rotation surviving the closed gallery pays constant energy unless it leaks from the common carrier.
  branching-plus-first-hit-exits-forces-hs-floor: that gives the abstract branching/exit mass ledger; this is the concrete six-edge unitary transport inequality and its exact constant on the four-atom carrier.
---

Let `(M_d,tr_d)` carry projections

```text
R_0,R_1,...,R_6,             R_6=R_0=R,
```

and contractions `B_i` supported from one carrier to the next:

```text
B_i=R_i B_i R_(i-1).                                    (HEL1)
```

Let `A_i` be the six raw unitary transition words around the `A_2` gallery,
in the order

```text
123 -> 213 -> 231 -> 321 -> 312 -> 132 -> 123,
```

and put

```text
Omega=A_6 A_5 ... A_1.                                  (HEL2)
```

Define the supported transition errors

```text
e_i=||(B_i-A_i)R_(i-1)||_2.                             (HEL3)
```

The product of the decoded transitions obeys the dimension-free telescoping
bound

```text
||B_6...B_1-Omega R||_2 <= sum_(i=1)^6 e_i.             (HEL4)
```

Indeed expand the difference one factor at a time.  Every decoded prefix has
operator norm at most one and range in the next carrier by `(HEL1)`; every
raw suffix is unitary.  The `i`-th summand is therefore bounded by `(HEL3)`.
No word length, spectral period, carrier rank, or ambient dimension appears.

For the actual root words

```text
n_12=x_12(1)x_21(-1)x_12(1),
n_23=x_23(1)x_32(-1)x_23(1),
Omega=(n_12n_23)^3,                                    (HEL5)
```

the group identity is `Omega=1`.  In a matrix tuple of presentation defect
`epsilon`, van Kampen telescoping gives

```text
||(Omega-I)R||_2 <= A_Omega epsilon                      (HEL6)
```

for one fixed finite area `A_Omega`.  Combining `(HEL4)--(HEL6)` gives

```text
||B_6...B_1-R||_2
 <= sum_i e_i + A_Omega epsilon.                         (HEL7)
```

## Four-atom holonomy floor

Suppose the decoded product is a unitary `K` on `RH` and there are commuting
projections `P,Q<=R` such that

```text
tr(P)=tr(Q)=tr(R)/2,
tr(PQ)=tr(R)/4,
K P K^*=Q.                                              (HEL8)
```

Writing `mu=tr(R)`, independence gives

```text
||Q-P||_2^2=mu/2.                                       (HEL9)
```

On the other hand

```text
||KPK^*-P||_2 <= 2||(K-I)R||_2.
```

Therefore

```text
||(K-I)R||_2^2 >= mu/8.                                 (HEL10)
```

Together with `(HEL7)` and Cauchy--Schwarz,

```text
mu/8
 <= 2 (sum_i e_i)^2 + 2 A_Omega^2 epsilon^2
 <= 12 sum_i e_i^2 + 2 A_Omega^2 epsilon^2.             (HEL11)
```

Thus a role-rotating interior-overlap holonomy on positive carrier mass pays
a fixed normalized-HS energy, independently of all finite clock scales.

## Leakage form

If the raw transition does not remain in the proposed next carrier, define

```text
ell_i=||(I-R_i)A_iR_(i-1)||_2.                          (HEL12)
```

Taking `B_i=R_iA_iR_(i-1)` makes `e_i=ell_i`; allowing an additional rounded
transition adds its rounding error by the triangle inequality.  Consequently
`(HEL11)` becomes the exact dichotomy

```text
positive rotating carrier mass
  <= C (sum local rounding energy + sum conductor leakage
        + presentation defect squared),                (HEL13)
```

with a universal numerical coefficient for six edges and the one fixed word
area `A_Omega`.

Periodic Heisenberg/Weyl clocks therefore cannot defeat the **analytic**
holonomy estimate by increasing their period.  The fixed-period common packet
has zero holonomy by `six-chamber-a2-holonomy-closes-fixed-clock-sector`; the
chamber-separated countermodels keep a nontrivial role rotation only by
failing to place all six transitions on the same closed carrier, which is
exactly leakage in `(HEL12)`.

The sole remaining arithmetic task is to decode the carriers and charge that
leakage to conductor descent with constants suitable for fixed-depth
iteration.
