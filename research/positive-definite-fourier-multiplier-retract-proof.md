---
rg: 2
id: positive-definite-fourier-multiplier-retract-proof
kind: route
title: Put a positive-definite Fourier multiplier in the hidden diagonal block
target: matrix-homogeneous-ucp-retracts-can-hide-defect
requires: []
---

Let `(pi_f,H_f,xi_f)` be the GNS representation of the normalized
positive-definite function `f`.  Tensoring the canonical
`alpha`-projective representation with the ordinary representation `pi_f`
preserves multiplier `alpha`; compression by `xi_f` sends
`u_g` to `<pi_f(g)xi_f,xi_f>u_g=f(g)u_g`.  Hence `M_f` is ucp on the full
twisted group algebra.

The direct-sum map `i_f=id direct_sum M_f` and top-left compression `r` are
ucp and split exactly.  Their restrictions to the homogeneous `g`-line are
given by `(MHR2)`, so they intertwine the canonical coaction.  If
`|f(g)|<1`, then

```text
1-i_f(u_g)^*i_f(u_g)
 =diag(0,(1-|f(g)|^2)1)>0,
```

and top-left compression kills this defect.

For `G=Z/2`, the matrix `[[1,t],[t,1]]` is positive for `|t|<=1`, proving
positive definiteness of `f_t`.  Formula `(MHR2)` then gives the stated
operator-norm distance to the scalar homogeneous line and the nonzero defect
at every `t<1`.
