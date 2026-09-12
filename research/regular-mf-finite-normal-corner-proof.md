---
rg: 2
id: regular-mf-finite-normal-corner-proof
kind: route
title: Cut the regular MF model by the finite-kernel averaging projection
target: regular-mf-descends-finite-normal-quotients
requires: []
---

Let maps `sigma_k:G -> U(d_k)` witness that `delta_G` is MF.  They give a
homomorphism

```text
rho:G -> U(Q),          Q=prod_k M_(d_k) / direct-sum_k M_(d_k),
```

and the normalized coordinate traces converge to `delta_G` on `rho(G)`.
Inside `Q` form the exact averaging projection

```text
p=(1/|F|) sum_(f in F) rho(f).                          (FNC1)
```

Normality of `F` makes `p` commute with `rho(G)`, and `p rho(f)=p` for every
`f in F`.  The regular trace calculation gives

```text
tau(p)=1/|F|.                                            (FNC2)
```

Lift `p` to projections `p_k in M_(d_k)`.  Then
`rank(p_k)/d_k -> 1/|F|`, and the corner is again a matrix corona:

```text
pQp = prod_k p_k M_(d_k) p_k / direct-sum_k p_k M_(d_k) p_k.   (FNC3)
```

With unit `p`, the formula

```text
bar_rho(gF)=p rho(g) p                                  (FNC4)
```

is a well-defined homomorphism `G/F -> U(pQp)`.  Normalize the corner trace
by `(FNC2)`.  For every `g in G`,

```text
tau_p(bar_rho(gF))
 = |F| tau(p rho(g))
 = sum_(f in F) tau(rho(fg))
 = 1  if g in F, and 0 otherwise.                       (FNC5)
```

Thus `(FNC4)` has the regular character of `G/F`.  Choosing matrix
representatives for the countably many unitaries in `(FNC4)`, polar
correcting them, and diagonalizing over finite multiplication tables gives
operator-norm asymptotic unitary representations in the finite corners
`p_k M_(d_k) p_k` with the traces in `(FNC5)`.  Hence `delta_(G/F)` is an MF
character.

The argument uses regular trace convergence essentially.  Without it the
projection `(FNC1)` may have zero rank germ, which is exactly why this proof
does not conflict with `mf-quotient-nonclosure`.
