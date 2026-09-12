---
rg: 2
id: fournier-facio-fixed-block-haar-moment-proof
kind: route
title: Compute every charged power moment on the nonsofic fixed sector
target: fournier-facio-fixed-block-actor-is-charge-haar
requires:
  - fournier-facio-fixed-block-spectrum-escapes
---

Let `p(T)^2=phi_mu(T^*T)` be the charged column seminorm.  Repeated near
multiplication and invariance of the state give

```text
p(B_g^n-B_(g^n))=0                              (n>=1). (FFHP1)
```

For `n!=0`, torsion-freeness gives `g^n!=1`.  Essential freeness says that
for every `epsilon>0`, the set on which the absolute diagonal coefficient of
`B_(g^n)` exceeds `epsilon` is null.  Hence

```text
phi_mu(P_F B_(g^n) P_F)=0.                            (FFHP2)
```

The charged column equality `(FFHP1)` first transfers the same pointwise
diagonal conclusion to `B_g^n`, proving `(FFHM3)`.  (Right compression by
`P_F` is harmless here because it is a diagonal basis projection.)
Cauchy--Schwarz for the Hilbert-space inner product gives

```text
<U^i delta_x,U^j delta_x>=<delta_x,U^(j-i) delta_x>.
```

Taking the finite union over `0<=i<j<=N` proves `(FFHM4)`.
Cauchy--Schwarz for `phi_mu` then replaces `B_(g^n)` by `B_g^n` in
`(FFHP2)`.  Since `P_F` commutes with `B_g`, this is precisely
`psi(U^n)=0`.  The case `n<0` is its complex conjugate, and `psi(1)=1`.
By uniqueness of measures from Fourier coefficients, the spectral law of
`U` under `psi` is Haar.
