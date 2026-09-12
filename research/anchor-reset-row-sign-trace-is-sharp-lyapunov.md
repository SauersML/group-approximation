---
rg: 2
id: anchor-reset-row-sign-trace-is-sharp-lyapunov
kind: claim
title: Anchor row energy plus eight times negative-sign mass is a sharp reset Lyapunov
distinct_from:
  spectral-cut-anchor-reset-pays-boundary-in-one-row: that gives a one-step triangle upper bound in terms of the cut boundary; this gives the exact signed block-energy change and a monotone augmented potential.
  odd-spectral-anchor-resets-have-monotone-sign-budget: that telescopes only the removed negative trace; this proves that the commutator boundary created by a reset is absorbed by that same budget.
  central-adaptive-peeling-or-noncentral-stopping: that still needs coverage and a small-error terminal estimate; this removes literal row-boundary recycling for sequential resets of one anchor.
---

ESTABLISHED.  Let `A,B_1,...,B_m` be reflections, let `p` be a projection
commuting with `A`, and reset

```text
 A'=p+(1-p)A.
```

Put

```text
 e=(1-A)/2,   s=pe,   r=(1-p)e,   t=1-e,
 E_B(A)=(1/m)sum_k ||[A,B_k]||_2^2.                    (ARL1)
```

Then `(1-A')/2=r` and the exact change is

```text
 E_B(A')-E_B(A)
 =8 avg_k ( ||sB_k r||_2^2-||tB_k s||_2^2 ).          (ARL2)
```

Consequently

```text
 [E_B(A')+8tau((1-A')/2)]
 -[E_B(A) +8tau((1-A )/2)]
 =-8 avg_k( ||sB_k s||_2^2+2||tB_k s||_2^2 ) <=0.    (ARL3)
```

Thus an anchor's averaged commutator-row energy plus eight times its
negative-sign trace is nonincreasing under every commuting-block reset.
No assumption that successive cuts commute is needed.  Applying `(ARL3)`
successively shows that all row energy created through nonreducing cut
boundaries is paid by the monotone negative-sign reservoir.

The coefficient `8` is sharp for arbitrary reflection families.  In `M_2`,
take

```text
 A=-I,  p=diag(1,0),  B=[[0,1],[1,0]].                 (ARL4)
```

The old commutator energy is zero, the new one is `4`, and the normalized
negative trace falls by `1/2`.  Hence
`E_B+c tau((1-A)/2)` increases whenever `c<8`, while equality holds at
`c=8`.  Repeating this `B` among a growing reflection family shows the same
sharp uniform constant when the row average also contains the anchor itself.

For the normalized complete-pair energy

```text
 E_pair=L^(-2)sum_(i,j)||[Q_i,Q_j]||_2^2,
```

changing only anchor `a` changes the two symmetric ordered rows.  Therefore
the corresponding global Lyapunov contribution is

```text
 E_pair +(16/L)tau((1-Q_a)/2),                          (ARL5)
```

up to the unchanged rows (equivalently use unordered pairs and coefficient
`8/L`).

This resolves boundary *recycling*, but not the whole basin theorem.  The
initial sign reservoir can have order-one trace, so `(ARL3)` alone yields an
`O(1)` rather than `o(E)` bound.  The remaining coverage theorem must use
the odd-spectral balance `tau(pe)=tau(p)/2` and the Loewner row charge to
show that only vanishing trace-weighted cut mass is actually consumed, or
that a geometric energy stage terminates before an order-one part of the
reservoir is spent.
