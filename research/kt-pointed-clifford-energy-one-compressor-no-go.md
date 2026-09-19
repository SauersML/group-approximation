---
rg: 2
id: kt-pointed-clifford-energy-one-compressor-no-go
kind: claim
title: The pointed Clifford wall energy has canonical one-compressor matrix countermodels
distinct_from:
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: that proves the actor leg of the one-compressor wreath microstates is not correctable; this extracts the exact scalar wall profile carried by those microstates and uses it to refute every one-compressor pointed transfer modulus.
  trace-zero-involution-projective-transfer-equals-rcc: that shows abstractly that trace-zero involutions do not weaken qualitative relative-commutant collapse; this gives source-specific canonical permutation countermodels with ordinary commutator energy exactly matching the Clifford Majorana profile.
  kun-thom-clifford-relative-wall: that asks for anticommuting conjugate lamps together with the full Kun--Thom actor; this omits anticommutation and the other compressors, and proves that this weaker pointed-energy target is already satisfiable in matrices.
---

Use the `q=2`, `d=3`, `r>=5` Kun--Thom pair, fix one strict positive
compressor `t`, put

```text
V=<Gamma,t>,                  Lambda=t Gamma t^(-1),
```

and choose `gamma_0 in Gamma minus Lambda`.  In the canonical Clifford
crossed product let

```text
x_Cl=c_(t Gamma).
```

Then `x_Cl` is a trace-zero self-adjoint involution, centralizes `Lambda`,
and has the pointed wall energy

```text
||[x_Cl,u_(gamma_0)]||_2^2=2.                          (PCE1)
```

This entire scalar profile already has canonical finite-matrix models over
the **one-compressor** actor.  More precisely, there are canonical
regular-trace normalized-HS microstates `rho_n` of `V` and matrices `X_n`
such that

```text
||X_n-X_n^*||_2+||X_n^2-I||_2+|tr(X_n)| -> 0,
max_(s in S_Lambda)||[X_n,rho_n(s)]||_2 -> 0,
||[X_n,rho_n(gamma_0)]||_2^2 -> 2,                    (PCE2)
```

for any fixed finite generating set `S_Lambda`, while the actor
multiplication defects tend to zero on every fixed window.

Consequently there is no dimension-independent modulus `omega(delta)->0`
bounding the final energy in `(PCE2)` by the actor presentation defect plus
the involution, trace, and `Lambda`-centrality defects.  This remains false
after imposing the canonical regular trace on every fixed actor word.

Thus the weakest pointed ambient-complement inequality is too weak.  A
matrix-ultraproduct exclusion of the actual Clifford wall must consume data
absent from this countermodel: either the operator relation

```text
x_Cl (u_(gamma_0)x_Clu_(gamma_0)^*)
 =-(u_(gamma_0)x_Clu_(gamma_0)^*)x_Cl,
```

or relations involving enough additional compressors to recover the full
nonamenable actor.  The scalar second moment alone cannot distinguish the
Clifford wall from an ordinary binary Bernoulli wall.
