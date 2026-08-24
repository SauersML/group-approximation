---
rg: 2
id: glue-lemma-escape-clause-void-proof
kind: route
title: Add half a fresh dictator, keep the heavy cosets, and buy the escape clause
target: glue-lemma-escape-clause-voids-the-conclusion
requires: []
---

Let `f : {-1,1}^Omega -> [-1,1]` satisfy the hypotheses of the glue lemma
with heaviness `delta` on the direction set `B` and centres `q_b`.  Choose
`z in Omega` with `hat g(z) = 0`, where `g = T_rho f`; such a `z` exists
whenever `g` is not linearly supported on all of `Omega`, and in any case
one may enlarge `Omega` by one unused coordinate.  Put

```text
f' = ( X_z + f )/2.
```

**Range.**  `|f'| <= (|X_z| + |f|)/2 <= 1`, so `f'` maps into `[-1,1]`.

**The escape clause fires.**  `T_rho` is linear and `T_rho X_z = rho X_z`,
so `g' = T_rho f' = (rho X_z + g)/2` and `hat{g'}(z) = rho/2 + hat g(z)/2 = rho/2`.
Hence `Inf^{<=d}_z(g') >= (rho/2)^2 = rho^2/4`, a constant independent of
`k`.  So `f'` has a large ambient low-degree influence and the clause
applies to it.

**The hypotheses survive.**  Restriction is linear and
`X_z|_{D_b} = Y_{[z]_b}`, so

```text
g'|_{D_b} = ( rho * Y_{[z]_b} + g|_{D_b} ) / 2.
```

The added term is supported on the single quotient coordinate `[z]_b`, so
for any coset `C != [z]_b` every Fourier coefficient of `g'|_{D_b}` on a set
containing `C` is exactly half the corresponding coefficient of `g|_{D_b}`.
Therefore, for every `b in B` with `z notin C_b`,

```text
Inf^{<=d}_{C_b}( g'|_{D_b} ) = (1/4) Inf^{<=d}_{C_b}( g|_{D_b} ) >= delta/4.
```

The condition `z notin C_b` fails only when `q_b in {z, z+b}`.

**Conclusion.**  `f'` satisfies the hypotheses with heaviness `delta/4` and
the same centres `q_b`, so producing a bounded `Q` for `f'` is exactly as
hard as producing one for `f`; but the statement carrying the escape clause
says nothing about `f'`.  A decoder taking the escape branch receives
`Q = {z}`, which meets `C_b` only when `q_b in {z, z+b}` -- a fraction
`O(1/N)` of `B` whenever the centres are spread, hence `gamma -> 0`.

The perturbation costs the adversary one coordinate and is available for
every `f`, so the clause is not a hedge on a hard case: it is a hole in the
statement.  Deleting it yields the strictly stronger form, which is what
`glue-lemma-holds-for-quadratic-functions` already proves at ambient degree
two with `gamma = 1`.
