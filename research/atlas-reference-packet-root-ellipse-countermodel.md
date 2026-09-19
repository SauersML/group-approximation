---
rg: 2
id: atlas-reference-packet-root-ellipse-countermodel
kind: claim
title: The exact A4 reference alignment has root-ellipse energy seventy-three
artifacts:
  - experiments/atlas_a4_reference_alignment.py
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that corrected endpoint additionally assumes the collision relation tends to one; this is an exact counterexample to omitting that independent hypothesis.
---

Let `rho_k=Reg(A8) tensor I_k`, and let `r_0 in A8` be the fixed inner packet
alignment of `atlas-a4-packet-centralizer-product-compiler`.  Thus

```text
r_0=
[0 0 0 1]
[0 1 0 0]
[1 0 0 0]
[0 0 1 0]
```

over `F_2`.  Put `U_k=rho_k(r_0)`.  For every `k>=1`, the two chart
representations `rho_k` and `Ad(U_k) o rho_k` satisfy all thirty shortest A4
pair-cubes exactly and have exact regular type at both chart vertices.

Nevertheless all four root deficits equal one:

```text
x_01(U_k)^2=x_12(U_k)^2=x_23(U_k)^2=x_30(U_k)^2=1.
```

Consequently

```text
S(U_k)=2+2+4=8,
S(U_k)^2+S(U_k)x_12(U_k)+x_12(U_k)^2=73.              (A4-REF-ELLIPSE)
```

Taking any sequence `k_n`, including `k_n->infinity`, gives a normalized
exact-regular A4 packet sequence with root functional constantly `73`, far
above `3/128`.  Therefore no root-energy ceiling follows from packet
normalization alone.  The independent hypothesis
`||q_19243(U_n)-1||_2->0` is logically indispensable.
