---
rg: 2
id: stw09-bratteli-trace-shadowing-proof
kind: route
title: Pull later weights backwards and take the summable-error limit
target: stw09-summably-balanced-bratteli-models-give-af-embedding
requires:
  - stw09-trace-preserving-af-embedding-iff-trace-coherent-models
artifacts:
  - research/artifacts/stw09-summably-balanced-bratteli-model-audit-2026-08-30.md
---

The dimension equations make `alpha_n` unital, and every nonzero source
column makes it injective.  If a trace on `F_(n+1)` has central weight vector
`v`, direct evaluation on the central unit of the `i`-th summand gives

```text
sigma_v alpha_n
 = sigma_(P_n v).
```

For each target index `j`, summing the coefficient of `v_j` over `i` gives
`1` by the dimension equation, so `P_n` sends probability vectors to
probability vectors.  More invariantly,
`P_n` is pullback of traces along a unital star homomorphism, so it is a
contraction for trace norm.  In central-weight coordinates that norm is
exactly the `l1` norm.

For `m>n`, write

```text
P_(n,m)=P_n P_(n+1) ... P_(m-1).
```

Put `e_l=||w_l-P_l w_(l+1)||_1`.  Contractivity gives

```text
||P_(n,m+1)w_(m+1)-P_(n,m)w_m||_1 <= e_m.
```

Because `sum_m e_m<infinity`, the sequence `P_(n,m)w_m` is Cauchy for each
fixed `n`.  Let

```text
tilde_w_n = lim_(m->infinity) P_(n,m)w_m.
```

Every `tilde_w_n` is a probability vector, continuity gives

```text
P_n tilde_w_(n+1)=tilde_w_n,
```

and telescoping gives the quantitative shadowing bound

```text
||tilde_w_n-w_n||_1 <= sum_(m>=n)e_m -> 0.            (BTS1)
```

Let `tilde_sigma_n` be the trace on `F_n` with weight vector `tilde_w_n`.
The first displayed compatibility says exactly

```text
tilde_sigma_(n+1) alpha_n=tilde_sigma_n.
```

Moreover, for `a` in the unit ball, `(BTS1)` gives

```text
|tilde_sigma_n psi_n(a)-sigma_n psi_n(a)|
 <= ||tilde_w_n-w_n||_1 -> 0.
```

Hence `tilde_sigma_n psi_n(a)->tau(a)` for every `a`.

The maps `psi_n`, embeddings `alpha_n`, exact traces `tilde_sigma_n`, and
the given summable norm-coherence errors now satisfy
`stw09-trace-preserving-af-embedding-iff-trace-coherent-models`.
Consequently they define a homomorphism `Phi:A->lim(F_n,alpha_n)` and a
limit trace `sigma` with `sigma Phi=tau`.  Faithfulness of `tau` makes
`Phi` injective.

No surjectivity of the pullback maps `P_n` is used.  This matters: a proposed
stage trace need not extend to the next finite-dimensional algebra.  The
argument obtains the exact compatible thread as a limit of traces pulled
back from arbitrarily late stages instead.
