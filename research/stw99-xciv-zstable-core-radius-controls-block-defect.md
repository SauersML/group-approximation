---
rg: 2
id: stw99-xciv-zstable-core-radius-controls-block-defect
kind: claim
title: Distance to a Jiang--Su-stable norm core bounds the fixed-block defect
distinct_from:
  stw99-xciv-commutant-capacious-radius-controls-block-defect: that theorem approximates by cores with an exact commuting I_(2,3) in the ambient factor; this theorem uses approximate central copies internal to a Z-stable core and allows the core to have scalar ambient relative commutant.
  stw99-xciv-norm-matrix-tower-has-zstable-hull: that theorem constructs one Z-stable AF hull from a coherent matrix tower; this theorem applies to arbitrary already-Z-stable subalgebras, including weakly dense non-AF finite-nuclear-dimension cores.
  stw99-xciv-some-finite-tuple-has-positive-fd-radius: that theorem obstructs finite-dimensional norm approximation for some tuple; the present estimate uses infinite-dimensional regular cores and is independent of finite-dimensional radius.
  stw99-xciv-single-prime-block-centrality-is-exact: that theorem characterizes separable Z-stability globally; this theorem gives a quantitative local class inside R and an explicit scalar-commutant example.
artifacts:
  - research/artifacts/stw99-xciv-zstable-core-radius-audit-2026-08-30.md
---

Fix `D=I_(2,3)` and its finite self-adjoint contractive generating set `H`.
For finite `F subset R`, define

```text
zeta_Z(F)=inf_A max_(a in F) dist(a,A),                  (1)
```

where `A` ranges over separable unital `Z`-stable C*-subalgebras of `R`.
Then

```text
gamma_D(F)<=2 zeta_Z(F).                                (2)
```

Thus every finite tuple contained in, or arbitrarily norm-close to varying,
separable `Z`-stable norm cores has zero fixed-block defect.  In particular
this applies whenever `F` is contained in a separable simple unital nuclear
infinite-dimensional finite-nuclear-dimension subalgebra of `R`, since such
an algebra is `Z`-stable.

This mechanism does not require a large ambient relative commutant.  There
is a unital trace-preserving embedding

```text
pi_tau:Z->R
```

whose range is weakly dense.  Hence

```text
pi_tau(Z)' intersect R=C1,                              (3)
```

while every finite `F subset pi_tau(Z)` has

```text
gamma_D(F)=0.                                           (4)
```

Therefore a large relative commutant of the **chosen containing core** is not
required for local fixed-block centralization: a weakly dense regular norm
core can manufacture the copies internally.  No claim is made that the same
finite tuple has positive `beta_D` relative to every other possible core.

Conversely, a negative certificate `gamma_D(F)>=delta` must satisfy

```text
zeta_Z(F)>=delta/2.                                     (5)
```

It must be uniformly separated in operator norm from every separable
`Z`-stable subalgebra of `R`, not only from finite-dimensional algebras and
tensor-split cores.

The assertion that `zeta_Z(F)=0` for every finite `F subset R` is exactly a
strong local form of XCIV and is not proved here.
