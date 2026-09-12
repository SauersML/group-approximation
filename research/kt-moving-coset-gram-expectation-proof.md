---
rg: 2
id: kt-moving-coset-gram-expectation-proof
kind: route
title: Write the matrix conditional expectation as an L2 projection quotient
target: kt-edge-expectation-is-a-moving-coset-gram-supremum
requires: []
---

The finite-dimensional algebra `B_n` is the `L2(M_(d_n),tau_n)` closure of
the linear span of the unitaries `rho_n(gamma)`, `gamma in Gamma`.  For

```text
b_c=sum_gamma c_gamma rho_n(gamma)
```

one has, using exact multiplicativity and the tracial inner product,

```text
||b_c||_2^2=N_n(c),
<b_c,rho_n(g)> =L_(n,g)(c).                            (KCG4)
```

Orthogonal projection onto a closed subspace `V` obeys

```text
||P_V(x)||^2=sup_(v in V, v!=0) |<v,x>|^2/||v||^2.
```

Apply this with `V=L2(B_n)` and use the spanning family above.  This gives
`(KCG3)`.

If `chi_n` converges pointwise to the regular character, then for fixed
finite support and `g notin Gamma`, every term
`chi_n(gamma^(-1)g)` in the numerator tends to zero, while the denominator
tends to `sum_gamma |c_gamma|^2`.  This proves fixed-vector vanishing.

For the profinite calibration, `h in cl_profinite(Gamma)` means that in each
finite quotient used at stage `n`, its image equals the image of some
`gamma_n in Gamma`.  Hence `rho_n(h)=rho_n(gamma_n)` and the single
coefficient vector supported on `gamma_n` has numerator and denominator both
equal to one.  The supremum is therefore one at every stage.

