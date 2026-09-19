---
rg: 2
id: kt-elementary-kazhdan-packet-rounding-proof
kind: route
title: Apply the adjoint Kazhdan gap and spectrally round the conditional expectation
target: kt-elementary-kazhdan-packet-rounds-base-lamp
requires:
  - kun-thom-nonsofic-wreath
  - kt-ab-marked-return-is-the-first-mixed-cylinder
  - kt-single-root-mixed-return-has-exact-finite-countermodels
---

The Steinberg identities

```text
e_ij(f)e_ij(g)=e_ij(f+g),
[e_ik(f),e_kj(g)]=e_ij(fg)
```

show inductively on monomial degree that `(KEP1)` generates every
`e_ij(f)` with `f in F_q[x_1,x_2,x_3]`, hence generates `Gamma`.  Property
`(T)` from the pinned Kun--Thom theorem therefore gives a positive Kazhdan
constant `kappa_K` for this finite generating packet.

Apply `pi` by conjugation to the normalized Hilbert--Schmidt space
`L^2(M_d)`.  Its invariant subspace is exactly `pi(Gamma)'`.  If `E` denotes
orthogonal projection onto that subspace, the Kazhdan inequality gives

```text
||P-E(P)||_2 <= kappa_K^(-1) max_(s in K)||[P,pi(s)]||_2. (KEP5)
```

Put `X=E(P)`.  Conditional expectation is positive and unital, so
`0<=X<=1`.  Let `P_0=1_[1/2,1](X)`.  Orthogonality of `P-X` to the commutant
and `tr(PX)=tr(X^2)` give

```text
||P-X||_2^2=tr(X-X^2).
```

Pointwise on `[0,1]`, the squared distance to `{0,1}` is at most `x(1-x)`.
Consequently `||X-P_0||_2<=||P-X||_2`; Pythagoras proves `(KEP2)`.  The trace
claim follows from normalized Cauchy--Schwarz.

For `(KEP4)`, triangle inequality gives

```text
||[P,pi(s)]||_2 <= ||[P,u_s]||_2+2||u_s-pi(s)||_2.
```

Conjugating a contraction by two unitaries changes it by at most twice their
Hilbert--Schmidt distance.  Insert `(KEP2)` and apply the triangle inequality
to `Q`, `u_hPu_h^*`, `pi(h)Ppi(h)^*`, and
`pi(h)P_0pi(h)^*`.  This is exactly `(KEP4)`.
