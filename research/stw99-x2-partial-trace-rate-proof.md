---
rg: 2
id: stw99-x2-partial-trace-rate-proof
kind: route
title: A single operator-valued partial-trace cut replaces all matrix-entry cuts
target: stw99-x2-local-afd-at-partial-trace-rate
requires: []
artifacts:
  - research/artifacts/stw99-x2-2026-literature-and-route-audit-2026-08-31.md
---

Put `d_i = E_M(y_i)` and `z_i = y_i-d_i`, so
`||z_i||_2 <= delta`.  We first use the following elementary block
inequality.  If `X = (X_ab) >= 0` lies in `M_d bar-tensor N` and
`T_X = sum_a X_aa in N`, then

```text
X <= d (1 tensor T_X).                                      (1)
```

Indeed, write `X = V*V` with operator columns `V_a`.  For
`xi=(xi_1,...,xi_d)`, Cauchy--Schwarz gives

```text
<X xi,xi> = ||sum_a V_a xi_a||^2
           <= d sum_a ||V_a xi_a||^2
           =  d sum_a <X_aa xi_a,xi_a>
           <= d sum_a <T_X xi_a,xi_a>.
```

The constant is optimal.  In `M_d tensor M_d`, take
`Omega=sum_a e_a tensor e_a` and `X=|Omega><Omega|`.  Then
`T_X=sum_a X_aa=1`, while `||X||=||Omega||^2=d`; equality holds in
(1).  Consequently no refinement of this block inequality alone can remove
the remaining matrix-dimension loss.

For each `i`, apply (1) to `X_i^r=z_i* z_i` and
`X_i^l=z_i z_i*`, and put

```text
T = sum_i (T_(X_i^r) + T_(X_i^l)) in N_+.
```

With `tau = tr_d tensor tau_N`,

```text
tau_N(T_(z_i* z_i)) = d ||z_i||_2^2,
tau_N(T_(z_i z_i*)) = d ||z_i||_2^2,
```

and hence `tau_N(T) <= 2 j d delta^2`.  Let

```text
q = 1_((epsilon^2/d),infinity)(T),   s = 1-q.
```

Chebyshev's inequality and the assumed rate give

```text
tau_N(q) <= (d/epsilon^2) tau_N(T)
          <= 2 j d^2 delta^2 / epsilon^2 <= 1/2.
```

Thus `s != 0`.  Since `sTs <= (epsilon^2/d)s`, (1) gives, for every
`i`,

```text
||(1 tensor s) z_i* z_i (1 tensor s)|| <= epsilon^2,
||(1 tensor s) z_i z_i* (1 tensor s)|| <= epsilon^2.
```

Equivalently, `||z_i s|| <= epsilon` and `||s z_i|| <= epsilon`.
Now regard `s` as `1 tensor s in R` and set
`B=M_d tensor C s`.  Since `d_i` commutes with `s` and `d_i s in B`,

```text
||[y_i,s]|| = ||[z_i,s]|| <= ||z_i s||+||s z_i|| <= 2 epsilon,
```

while contractivity of the trace-preserving expectation onto `B` gives

```text
||s y_i s-E_B(s y_i s)||
 <= ||s z_i s||+||E_B(s z_i s)|| <= 2 epsilon.
```

This is Popa's local-AFD witness.  The proof uses one spectral projection
in the relative commutant, rather than `2 j d^2` entrywise projections;
that removes three powers of `d` from the trace budget.  QED.
