---
rg: 2
id: maslov-diverging-positive-order-lift-proof
kind: route
title: Diagonalize the universal finite-k lifting theorem in the tracial quotient
target: maslov-central-regular-lifts-have-diverging-positive-order
requires:
  - deligne-maslov-sector-traces-are-central-regular
artifacts:
  - research/artifacts/maslov-generator-operator-system-lp-sources-2026-08-22.md
---

Write

```text
B=prod_n M_(d_n),
I_omega={(x_n):lim_omega ||x_n||_(2,d_n)=0}.
```

The bounded `2`-null sequences form a norm-closed two-sided ideal, and the
tracial matrix ultraproduct is `B/I_omega`.

Kavruk's finite-`k` lifting theorem says that every finite-dimensional
operator system has the `k`-lifting property for each fixed `k`.  Therefore,
for every `k>=1`, `(DPO1)` has a unital `k`-positive lift

```text
Phi^(k):S -> B,
Phi^(k)=(phi_n^(k))_n.                                  (DPO4)
```

Fix a self-adjoint basis `e_1,...,e_r` of `S` and bounded representatives
`X_n(j)` of `Theta(e_j)`.  Since every `(DPO4)` represents the same quotient
map, the set

```text
A_k={n:max_j ||phi_n^(k)(e_j)-X_n(j)||_2 < 1/k}          (DPO5)
```

belongs to `omega`.  Replace `A_k` by the decreasing finite intersections
`A_1 cap ... cap A_k`, still in `omega`.  Define

```text
k_n=max({k<=n:n in A_k} union {1})                      (DPO6)
```

and set `phi_n=phi_n^(k_n)`.  For every fixed `K`, the set on which
`k_n>=K` contains `A_K cap {n>=K}` and hence belongs to `omega`; thus
`k_n->_omega infinity`.  On the omega-large set `A_1` one has
`n in A_(k_n)`, so the basis error in `(DPO5)` is at most `1/k_n` there.
Outside `A_1` the arbitrary default `k_n=1` is irrelevant to the ultralimit.
Linearity and finite dimensionality show that `(phi_n)` represents `Theta`
on all of `S`.  This proves `(DPO2)`.

If `Theta` has trace `tau_eta`, quotient equality and
`|tr(a)|<=||a||_2` give `(DPO3)` directly.  No extra correction uses character
rigidity; rigidity identifies the limiting trace as `tau_eta`.

Finally, define `psi_n(x)=phi_n(x) tensor I_(m_n)`.  It is still unital and
`k_n`-positive.  Conversely, compression to any multiplicity coordinate
shows that if `psi_n` is `ell`-positive then `phi_n` is `ell`-positive; common
amplification does not improve the exact positivity order.  Under normalized
traces, every scalar moment and every normalized `2`-norm difference is
unchanged, while the target dimension becomes `m_n d_n`.  Since a map into
`M_D` is certified completely positive by `D`-positivity, no lower bound on
positivity order as a fixed fraction of target dimension can follow from
those amplification-invariant scalar data alone.
