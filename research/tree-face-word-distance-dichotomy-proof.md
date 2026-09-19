---
rg: 2
id: tree-face-word-distance-dichotomy-proof
kind: route
title: Round near-word face values by the square-root-two separation of distinct group unitaries
target: tree-face-balance-pays-word-or-multiplicative-defect
requires:
  - group-word-tree-face-balancing-collapses
---

Distinct group unitaries in a full group C-star algebra are separated by at
least `sqrt(2)`.  Indeed, if `x!=y`, the left regular representation and its
canonical trace give

```text
||u_x-u_y||_(C^*(G_0)) >= ||lambda_x-lambda_y||_2=sqrt(2). (1)
```

Suppose, toward a contradiction, that

```text
mu_V+3 gamma_V<delta_L:=min{sqrt(2),6/L^2}
                                  for V=P_12 and P_23.     (2)
```

Choose `epsilon>0` small enough that `(2)` remains true after replacing each
`gamma_V` by `gamma_V+epsilon`.  For every `g in V`, choose
`x_g in G_0` with

```text
q(x_g)=g,
||Phi(u_g)-u_(x_g)||<gamma_V+epsilon.                       (3)
```

The values of a ucp map on unitaries are contractions.  Therefore for every
`g,h in V`, telescoping `(3)` and then using `(WMD1)` gives

```text
||u_(x_g x_h)-u_(x_(gh))||
 <= ||u_(x_g x_h)-Phi(u_g)Phi(u_h)||
    +||Phi(u_g)Phi(u_h)-Phi(u_(gh))||
    +||Phi(u_(gh))-u_(x_(gh))||
 < 3(gamma_V+epsilon)+mu_V
 < sqrt(2).                                                   (4)
```

By `(1)`, the two group elements in `(4)` are equal.  Hence

```text
alpha_V:V->G_0,             alpha_V(g)=x_g
```

is a group homomorphism, and `(3)` already arranged
`q alpha_V(g)=g`.

The rounded homomorphisms are not literally restrictions of `Phi`, so their
compatibility must be proved.  If `g in P_2`, then `(3)` on the two faces
gives

```text
||u_(alpha_12(g))-u_(alpha_23(g))||
 < gamma_12+gamma_23+2 epsilon
 < 2 delta_L/3+2 epsilon < sqrt(2).                       (5)
```

For sufficiently small `epsilon`, `(1)` forces
`alpha_12|_(P_2)=alpha_23|_(P_2)`.  The Bass--Serre classification in
`group-word-tree-face-lift-classification-proof` now applies to these two
compatible group-word lifts: there is one `k in K=ker q` such that

```text
alpha_V(g)=k g k^(-1),       g in V, V=P_12,P_23.         (6)
```

Conjugate the original ucp map (not the rounded homomorphisms):

```text
Psi=Ad(u_k^*) o Phi.
```

Equations `(3)` and `(6)` show that on every tree-face group unitary

```text
||Psi(u_g)-u_g||<gamma_V+epsilon.                          (7)
```

But `three-face-ucp-balancing-needs-macroscopic-tree-motion` says that some
letter in the two tree faces has displacement at least `2/L^2` from its
canonical lift.  Letting `epsilon` tend to zero in `(7)` gives

```text
max_V gamma_V >= 2/L^2.                                   (8)
```

On the other hand `(2)` and `delta_L<=6/L^2` give
`gamma_V<delta_L/3<=2/L^2` on both faces, a contradiction.  Thus `(2)` is
impossible, proving `(WMD2)`.
