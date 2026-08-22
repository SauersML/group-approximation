---
rg: 2
id: all-dual-unique-neighbors-contract-operator-tails
kind: claim
title: All-local-dual unique neighbors contract noncentral commutator tails down to the bad-row floor
distinct_from:
  adjoint-parity-cone-lifts-to-loewner-order: that lifts fixed parity-row inequalities and a global max-fractional pseudodistance; this selects support-dependent dual rows and proves a robust distributional contraction.
  commutator-threshold-sets-need-not-be-stopping-sets: that rules out applying stopping expansion directly to every threshold set; this uses unique rows only to remove a fixed fraction from a higher threshold.
  dellm-all-dual-presentation-has-many-unique-neighbors: that is a scalar support theorem for the concrete code; this converts it into a noncentral normalized-HS tail inequality.
---

Let `H` be a labelled binary parity matrix of row width at most `w` and
column degree at most `D`, satisfying `(SUN2)` with constants `alpha,gamma`.
Let `Q_1,...,Q_L` be reflections.  Assume each parity-row face has already
been made commuting, and for a row `h` put

```text
e_h=||prod_(i in h) Q_i-I||_2.
```

Define the aggregate noncentral commutator magnitude

```text
q_i=((1/L) sum_j ||[Q_i,Q_j]||_2^2)^(1/2),
U_t={i:q_i>=t},
B_rho={h:e_h>rho},  b_rho=|B_rho|.                       (AUT1)
```

Whenever `|U_t|<=alpha L`, one has the dimension-independent tail
contraction

```text
|U_((w-1)t+2rho)|
 <= (1-gamma/D)|U_t| + b_rho/D.                          (AUT2)
```

The same conclusion holds with `q_i=||[Q_i,W]||_2` for any fixed bounded
operator `W`.  At zero defect it says that a small coordinate tail cannot
remain concentrated: at each multiplication of the threshold by `w-1`, a
fixed fraction of its sites disappears.

There is also an exact Loewner form of the shortened-core peeling step.
On `L_2(M)` put

```text
P_i=(I-Ad(Q_i))/2.
```

For a DELL​M vertex `v`, a coordinate set `W subset S(v)`, and
`s in W minus K_v(W)`, where `K_v(W)` is the union of supports of local
codewords supported in `W`, the all-local-dual presentation supplies a row
`h` with `h intersect W={s}`.  Exact local parity gives

```text
P_s <= sum_(i in h minus {s}) P_i
    <= sum_(i in S(v) minus W) P_i.                       (AUT3)
```

Thus all-local-dual separation genuinely strengthens the fixed-row Tanner
fundamental cone: it provides support-adaptive Loewner inequalities and,
after evaluating vector states, the robust tail recurrence `(AUT2)`.

This does not by itself prove same-Hilbert operator rounding.  It localizes
large coordinate tails to the bad-row floor, but supplies neither a common
spectral cut for the low diffuse remainder nor an inverse for the global
coordinate gradient.
---

The row family may be exponentially large in the fixed local packet size,
but `w,D` remain constants along the global code family, as required here.
