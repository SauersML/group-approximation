---
rg: 2
id: endpoint-zero-tail-marked-finite-model-proof
kind: route
title: Restrict the prefix action to the stationary zero tail and its one-prefix mate
target: endpoint-zero-tail-packet-has-marked-finite-model
requires:
  - endpoint-native-heads-retain-coordinate-q-s3-retract
  - endpoint-constant-root-enlargements-have-marked-finite-quotient
---

Let `Omega={0,1}^N` and let `V` be the `F_2`-vector space with basis
`Omega`.  Define

```text
s_i(omega)=i omega,
t_i(j omega)=omega if i=j, and 0 otherwise.           (1)
```

These operators satisfy

```text
t_i s_j=delta_ij,                  s_0t_0+s_1t_1=1,
```

so `(1)` is a representation of the binary Leavitt ring obtained directly
from its defining relations.

Set `alpha=000...` and `beta=1000...`.  Since adding or deleting any
positive number of leading zeroes fixes `alpha`, direct application of
`(1)` gives, for every `k>=1`,

```text
e_(0^k) alpha=c_k alpha=d_k alpha=p alpha=alpha,
e_(0^k) beta=c_k beta=d_k beta=p beta=0,

a_k alpha=beta,                   a_k beta=0,
b_k beta=alpha,                   b_k alpha=0,
q beta=beta,                      q alpha=0.           (2)
```

Thus the two-dimensional subspace `K=<alpha,beta>` is invariant under all
operators in `(ZTP1)`, with exactly the matrices stated there.

A depth-`k` partial Whitehead has entries built from `1`, the two adjacent
zero-prefix idempotents, and `c_k,d_k`.  Equation `(2)` therefore shows that
each of `P,J_1,J_2` preserves `K^20`.  The four nonconstant arm roots in
`(ZTP2)` have coefficients among `a_1,a_2,b_2,b_3`, so they preserve it as
well.  The native outward crossing uses `b_1`; all constant roots act only
on the 20-coordinate factor.  Finally `q` preserves `K`, proving invariance
under every generator in `(ZTP2)`.

All restrictions are invertible.  For roots this follows directly from
`x_ij(a)^2=1` in characteristic two; the partial Whiteheads are involutions;
and the remaining generators are products of these.  Hence restriction is
a group homomorphism into `GL(K^20)=GL_40(F_2)`, a finite group.

On either of the two tail sheets, `n,m` are the two standard coordinate
transvections on positions `7,8`, so their six-element subgroup remains
faithful.  On the `beta` sheet, `q` acts as one and therefore
`x_13(q)` is a nonidentity transvection.  This proves both marked assertions
and completes the all-word finite-model fence.
