---
rg: 2
id: iwahori-cuspidal-hecke-angle-proof
kind: route
title: Degeneracy-map Gram matrix plus Deligne gives the uniform cuspidal angle
target: iwahori-cuspidal-hecke-angle
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Work first at a torsion-free odd principal level `N=Gamma(m)`.  The two
degree-three degeneracy maps from the Iwahori cover give pullbacks
`res_1,res_2` on weight-two cuspidal cohomology.  With the Petersson norm and
the unnormalized Hecke convention,

```text
res_i^* res_i=3 I,                 res_1^* res_2=T_2.   (1)
```

Consequently, for cuspidal classes `f,g`,

```text
||res_1 f-res_2 g||^2
 =3||f||^2+3||g||^2-2 Re <f,T_2 g>.                    (2)
```

The operator `T_2` is normal because `2` is prime to the odd level: at full level `Gamma(m)` its Petersson adjoint is `T_2^* = <2>^(-1) T_2` with the diamond operator `<2>` unitary and commuting with `T_2` (it is selfadjoint only when that diamond acts trivially), and normality is all that the spectral bound below uses.
Eichler--Shimura identifies its eigenvalues with the weight-two Hecke
eigenvalues, and Deligne's Ramanujan--Petersson bound gives

```text
||T_2|| <= 2 sqrt(2).                                  (3)
```

Using `2||f||||g||<=||f||^2+||g||^2` in (2) proves

```text
||res_1 f-res_2 g||^2
 >= (3-2 sqrt(2))(||f||^2+||g||^2).                    (4)
```

Now let `M=Ad rho`, where `rho` is any finite-dimensional unitary congruence
representation.  Pass to an odd principal congruence kernel `N` acting
trivially on `M`, and write `Q=Gamma/N`.  Since `Q` is finite and the
coefficient field has characteristic zero, the Hochschild--Serre sequence and
averaging give

```text
H^1_cusp(Gamma,M)
  = (H^1_cusp(N,C) tensor M)^Q.                         (5)
```

The two degeneracy maps and `T_2 tensor 1_M` commute with the diagonal
`Q`-action.  Inequality (4) therefore holds on the full tensor product and
hence on its invariant subspace, with exactly the same constant and no
dependence on the level, `rho`, or its dimension.
