---
rg: 2
id: affine-haar-fourier-modulus-proof
kind: route
title: Recover the affine annihilator and homogenize its phase character
target: affine-haar-process-fourier-modulus-compiler
requires:
  - algebraic-compact-action-group-factor-compiler
---

Let `E=(F_p^I)^H` and let `D=E-hat` be its finitely supported dual.  If
`nu=m_(x_0+K)`, then

```text
hat(nu)(a)=chi_a(x_0) for a in K^perp, and 0 otherwise,
```

so `(AHF2)` is necessary.

Conversely assume `(AHF2)` and put

```text
S={a in D:|hat(nu)(a)|=1}.
```

Equality in the triangle inequality says that `chi_a` is constant
`nu`-almost surely for every `a in S`.  Products and inverses of constant
characters show that `S` is a subgroup and that

```text
z:S->mu_p,       z(a)=hat(nu)(a),
```

is a character.  Since `D` is an `F_p`-vector space, extend the corresponding
linear functional on `S` to `D`; Pontryagin duality gives `x_0 in E` with
`chi_a(x_0)=z(a)` on `S`.  Put `K=S^perp`.  Haar measure on `x_0+K` has the
same Fourier transform as `nu`, and characters determine measures, proving
`(AHF1)`.

Invariance of `nu` makes `A=x_0+K` invariant.  Formula `(AHF3)` defines a
closed subgroup because

```text
(t x_0+k,t)+(s x_0+l,s)=((t+s)x_0+(k+l),t+s).
```

For `g in H`, invariance of `A` gives `g x_0-x_0 in K`; hence coordinate
shift sends `(t x_0+k,t)` back into `K_tilde` and fixes its last coordinate.
Haar measure pushes to uniform measure on that coordinate and conditions to
affine Haar measure on every fiber.  Thus `q=1_{t=1}` is an invariant central
projection of trace `1/p`, and its crossed-product corner is exactly the
affine action crossed product.  If that corner is non-CE, the ambient algebra
in `(AHF4)` is non-CE.  The Fourier/Pontryagin identification in
`algebraic-compact-action-group-factor-compiler` then makes
`K_tilde-hat rtimes H` non-hyperlinear.
