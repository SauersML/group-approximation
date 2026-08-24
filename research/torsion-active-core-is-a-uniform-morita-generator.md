---
rg: 2
id: torsion-active-core-is-a-uniform-morita-generator
kind: claim
title: The reblocked torsion spectral corner uniformly generates every projective corona carrier
artifacts:
  - notes/EXACT_CORONA_DIMENSION_AND_HILBERT_HOTEL.md
---

**ESTABLISHED.**  In the active-core model supplied by
`torsion-normal-generator-has-full-support-corona-core`, write

```text
Q_k=(prod_n M_(k_n)(C))/(directSum_n M_(k_n)(C))
```

and let `p` be the active spectral projection of the finite-order normal
generator.  If the chosen normal-generation family has total length `L`,
then

```text
1_(Q_k) <=_MvN p^(directSum L).                       (UMG1)
```

Consequently `p` is full, `pQ_kp` is Morita equivalent to `Q_k`, and every
projection `q in Q_k` satisfies

```text
q <=_MvN p^(directSum L).                             (UMG2)
```

More generally, every projection in `M_t(Q_k)` is subequivalent to
`p^(directSum tL)`.  Thus every finitely generated projective corona module
admits a realization inside a number of copies of the one marked corner
which is linear in its original matrix-amplification degree and independent
of the coordinate dimensions.

In particular, all finite additive and Heisenberg packet projections of a
root representation can be placed in the fixed carrier `p^(directSum L)`.
The coefficient-module decoder therefore has no remaining growth-of-
stabilization obstruction.  Its unresolved content is compatibility of the
packet intertwiners and coefficient products on one common summand.

