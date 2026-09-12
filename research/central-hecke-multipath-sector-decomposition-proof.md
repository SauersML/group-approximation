---
rg: 2
id: central-hecke-multipath-sector-decomposition-proof
kind: route
title: Expand every centrally controlled word over the orthogonal Hecke atoms
target: central-hecke-controlled-multipaths-remain-sectorwise
requires:
  - spherical-quadrature-tensors-through-clifford-folner-windows
  - finite-projective-sector-groupoids-have-conjugate-absorbers
---

# Expand every centrally controlled word over the orthogonal Hecke atoms

Because the `p_a` are central, orthogonal, and sum to one,

```text
W_j W_j^*=sum_(a,b) p_a p_b V_(a,j)V_(b,j)^*=sum_a p_a=1,
```

and similarly `W_j^*W_j=1`.  In any product, insert `sum_a p_a=1`
between adjacent factors.  Orthogonality kills every summand whose atom
labels disagree, proving `(CHM2)`.  Taking the trace of `q^*q`, or of `q`,
gives the two formulas in `(CHM3)`.

For the arithmetic application, choose the spherical quadrature accuracy to
tend to zero with the coweight-box size.  The established Clifford Folner
construction gives sectorwise local defects `O(R^(-1/2))`, after the finite
projective groupoid cocycle is removed by conjugate doubling.  Equation
`(CHM3)` preserves the same bound after central control, independently of the
number and weights of the atomic quadrature sectors.  The spherical marker is
unchanged.  Hence the claimed sequence exists and no cross-sector payment can
be derived from this class of mixed operators.
