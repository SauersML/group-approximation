---
rg: 2
id: bcs-gap-blocks-vanishing-crt-mask-budget
kind: claim
title: A finite BCS gap forbids a vanishing global projection-CRT mask budget
distinct_from:
  independent-row-masks-transfer-bcs-gap-to-ambient-identity: that treats arbitrary predicate and consistency masks with approximate row errors; this specializes the theorem to exact projection-CRT cells and isolates the sharp forbidden-mass versus consistency-deficit dichotomy needed by the affine Frobenius route.
  projection-crt-deficit-forces-common-meet: that is a projection-lattice theorem for the incidences of one variable and contains no BCS predicate; this combines all variables and contexts through the finite game gap, without assuming that the resulting common meets commute.
  rowwise-hecke-crt-certificate-for-nonce-bcs: that asks for an ordinary group-algebra certificate with total budget strictly below the gap; this proves that no finite-dimensional family of rational CRT cells can satisfy that budget and quantifies exactly where its forbidden mass must go.
---

**ESTABLISHED.**  Fix a finite BCS with finite-dimensional gap `Delta>0`.
For each context let `(P_(c,a))_a` be a finite-dimensional PVM, put

```text
F_c=sum_(a forbidden)P_(c,a),
A_(c,x)=sum_a a_x P_(c,a),                            (BCM1)
```

and use the fixed question weights `mu_(c,x)` and
`mu_c=sum_(x in c)mu_(c,x)`.

Suppose that for every variable `x` there is a self-adjoint involution `B_x`,
and for every incidence `(c,x)` there is a projection `q_(c,x)`, such that

```text
(A_(c,x)-B_x)q_(c,x)=0.                               (BCM2)
```

Set

```text
D_con=sum_(c,x)mu_(c,x) tr(1-q_(c,x)),
V_forb=sum_c mu_c tr(F_c).                            (BCM4)
```

Then

```text
V_forb+D_con>=Delta.                                  (BCM5)
```

Consequently, if the total consistency-mask deficit tends to zero along any
sequence of rational matrix or finite group-algebra CRT cells, the weighted
forbidden mass obeys

```text
liminf V_forb>=Delta.                                 (BCM6)
```

There is no scalable global encoding with both vanishing consistency deficit
and vanishing forbidden mass.

More generally, suppose each context also has a predicate mask `s_c` with

```text
F_c s_c=0,
D_pred=sum_c mu_c tr(1-s_c).                          (BCM7)
```

Then `F_c<=1-s_c`, so

```text
V_forb<=D_pred,
D_pred+D_con>=Delta.                                  (BCM8)
```

The statement is robust in the form needed for canonical matrix
representatives.  With

```text
eta_c=||F_cs_c||_2,
eta_(c,x)=(1/2)||(A_(c,x)-B_x)q_(c,x)||_2,
delta_c=tr(1-s_c),
delta_(c,x)=tr(1-q_(c,x)),                            (BCM10)
```

one has

```text
Delta
 <=sum_c mu_c(eta_c+sqrt(delta_c))^2
   +sum_(c,x)mu_(c,x)
      (eta_(c,x)+sqrt(delta_(c,x)))^2.                 (BCM11)
```

Thus vanishing row errors and convergence of the mask traces pass directly
to `(BCM8)`; no separate stability theorem for the CRT projections is used.

Thus finitely many rational projection-CRT cells can preserve a positive
forbidden mass while their consistency deficits vanish, but that mass is at
least the original BCS gap.  Removing it with predicate masks spends at least
the same fixed budget.  In particular total mask deficit `o(1)` is impossible.

In the projection-CRT specialization, put `p_x=(1-B_x)/2` and assume the
masks reduce the context marginals.  Then

```text
r_(c,x)=((1-A_(c,x))/2)q_(c,x)
```

is a projection and `(BCM2)` is equivalent to

```text
p_xq_(c,x)=r_(c,x).                                   (BCM3)
```

For each variable, `projection-crt-deficit-forces-common-meet` then
additionally produces

```text
m_x=meet_(c contains x) r_(c,x),
tr(m_x)>=tr(p_x)-sum_(c contains x)tr(1-q_(c,x)).      (BCM9)
```

The projections `m_x` need not commute across variables, even when their
ambient context marginals do.  No commutativity claim is needed for `(BCM5)`:
the reflections `B_x=1-2p_x` already form the one shared-variable tuple on
which the ambient-identity BCS gap is tested.  This removes the apparent
global-meet loophole without turning the von Neumann meets into algebraic
group-ring projections.

DERIVATION
bcs-crt-mask-budget-proof
