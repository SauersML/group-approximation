---
rg: 2
id: canonical-hnn-flat-boundary-proof
kind: route
title: Tensor the regular HNN witness with a constant-coefficient finite regular representation
target: canonical-hnn-flat-boundary-enemy
requires: []
---

Let `lambda_G` be the left regular representation of `G`.  Residual
finiteness of `A` gives a finite quotient `q:A->Q` in which every member of
`S_A` is nonidentity.  The constant-coefficient construction in
`flat-singular-canonical-polar-proof` supplies a unit vector
`xi in ell^2(Q)` such that

```text
<lambda_Q(q(s))xi,xi>=alpha                 (s in S_A). (CHP1)
```

Work in

```text
M=L(G) tensor M_|Q|(C),
Pi(a)=lambda_G(a) tensor lambda_Q(q(a)),
P=1 tensor |xi><xi|.                                      (CHP2)
```

Under the identification `PMP = L(G) tensor C P`, equation `(CHP1)` gives

```text
P Pi(s)P=alpha (lambda_G(s) tensor P).                    (CHP3)
```

Since `alpha>0`, its unitary polar factor is
`rho_s=lambda_G(s) tensor P` and its modulus is `alpha P`.  Hence every
`mu_s` is zero.  Unitarity and `(CHP3)` give

```text
tau(P)^(-1)tau(P Pi(s)^*(1-P)Pi(s)P)
 =1-alpha^2.                                             (CHP4)
```

Set `U=lambda_G(t) tensor P`.  The tuple `(rho,U)` is literally the regular
tuple of `G` inside the normalized corner: every word has the same trace as
its left regular group unitary.  Thus all defining relators vanish and all
nonidentity word traces vanish.  For `c in C`, `[t,c]=1`; for `h in A-C`,
`[t,h]` is a nontrivial HNN-reduced word.  These facts prove `(CHB3)`--
`(CHB4)` and complete the claimed no-go.

