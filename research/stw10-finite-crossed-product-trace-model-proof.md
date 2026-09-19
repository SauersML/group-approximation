---
rg: 2
id: stw10-finite-crossed-product-trace-model-proof
kind: route
title: Amplify trace models through the regular covariant matrix representation
target: stw10-finite-crossed-products-preserve-amenable-and-qd-traces
requires: []
---

Write `m=|G|`.  The regular covariant representation gives a unital
homomorphism

```text
rho:A rtimes G -> M_m(A)
```

such that, with rows and columns indexed by `G`, `rho(a)` is diagonal with
orbit entries `alpha_(h^-1)(a)`, while `rho(u_g)` is a permutation matrix.
For finite `G`, full and reduced crossed products agree.

Suppose first that `tau` has u.c.p. matrix models
`phi_i:A->M_(k_i)`, using normalized Hilbert--Schmidt multiplicative defects
for amenability or operator-norm defects for quasidiagonality.  Define

```text
Phi_i=(id_(M_m) tensor phi_i) compose rho:
      A rtimes G -> M_(m k_i).                                 (3)
```

These maps are u.c.p.  To check multiplicativity on a finite set, first
approximate it by finite Fourier sums.  Collect the finitely many entries of
their `rho`-matrices and every entry-product occurring in matrix
multiplication.  Choose `phi_i` multiplicative on this finite packet.  Each
entry of

```text
Phi_i(xy)-Phi_i(x)Phi_i(y)
```

is a sum of at most `m` multiplicative defects of `phi_i`.  The elementary
matrix estimates

```text
||X|| <= m max_(r,s)||X_(r,s)||,
||X||_(2,M_m(M_k))^2=(1/m) sum_(r,s)||X_(r,s)||_(2,M_k)^2
```

therefore make the defect tend to zero in the relevant norm.  Contractivity
then absorbs the initial Fourier approximation.  This proves the required
multiplicativity of `(3)` in both cases.

For a Fourier monomial, the normalized matrix trace satisfies

```text
tr_(m k_i)(Phi_i(a u_g))
 = 0                                                    if g is not e,
 = (1/m) sum_(h in G) tr_(k_i)(phi_i(alpha_(h^-1)(a)))  if g=e.
```

The second line converges to `tau(a)` by invariance, and the first equals
`sigma(a u_g)`.  Linearity and Fourier density give convergence to `sigma`
on all of `A rtimes G`.  Thus either approximation property of `tau` passes
to `sigma`.

Conversely, restricting u.c.p. models for `sigma` to the canonical copy of
`A` gives models for `sigma|A=tau`, in the same norm.  This proves both
equivalences in `(1)`.

It remains to justify the Rokhlin assertion.  Let `omega` be any trace on
`A rtimes G` and put `tau=omega|A`; traciality makes `tau` invariant.  Fix
`g` different from the identity and `a in A`.  Given `epsilon>0`, choose
Rokhlin projections `(e_h)_(h in G)` which sum to `1`, are sufficiently
central on the orbit of `a`, and satisfy

```text
||alpha_g(e_h)-e_(g h)||<epsilon.
```

Cyclicity of `omega` gives

```text
omega(a u_g)
 = sum_h omega(e_h a u_g)
 = sum_h omega(e_h a u_g e_h).
```

Since `u_g e_h=alpha_g(e_h)u_g`, the norm of the `h`-th compressed term is
bounded, up to `||a|| epsilon`, by

```text
||e_h a e_(g h)||
 <= ||[a,e_(g h)]||,
```

because `e_h e_(g h)=0`.  Letting `epsilon` tend to zero gives
`omega(a u_g)=0`.  Hence `omega=tau compose E` on the dense Fourier
algebra, so every trace is canonical.

Finally, if `omega` is amenable, then its restriction `tau` is amenable.  If
all amenable traces on `A` are QD, `tau` is QD, and `(1)` makes `omega` QD.
This proves `(2)` entirely in operator norm after the amenability restriction
step.
