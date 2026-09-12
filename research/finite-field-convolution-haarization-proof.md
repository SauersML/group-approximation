---
rg: 2
id: finite-field-convolution-haarization-proof
kind: route
title: Raise every finite Fourier coefficient to a p-divisible power
target: finite-field-convolution-haarizes-affine-support
requires: []
---

The Pontryagin dual of `E` is the countable discrete vector space

```text
D=F_p^(Lambda x I)
```

of finitely supported coefficient arrays.  For `a in D`, write `chi_a` for
the corresponding character and

```text
hat(nu)(a)=integral chi_a(x) dnu(x).
```

Convolution multiplies Fourier transforms, so

```text
hat(nu^(star pn))(a)=hat(nu)(a)^(pn).                  (FCP1)
```

If `|hat(nu)(a)|<1`, the right side tends to zero.  Equality in the triangle
inequality shows that `|hat(nu)(a)|=1` exactly when `chi_a` is constant
`nu`-almost surely.  Its constant value is a `p`th root of unity, so the
`p`-divisible exponent in `(FCP1)` makes the value exactly one for every `n`.
Therefore the pointwise Fourier limit is

```text
1_S(a),   S={a : chi_a is constant on supp(nu)}.       (FCP2)
```

Continuity of `chi_a` upgrades almost-sure constancy to constancy on the
support.  It follows that

```text
S={a : chi_a(x-y)=1 for all x,y in supp(nu)}=K^perp,   (FCP3)
```

with `K` as in `(FCH2)`.  The Fourier transform of Haar measure `m_K` is
exactly `1_(K^perp)`.  Characters determine probability measures on the
compact metrizable abelian group `E`; hence `(FCP1)--(FCP3)` prove weak-star
convergence to `m_K`.  Shift invariance of `nu` makes its support and then
`K` shift invariant.

For exponents `pn+1`, the same calculation has limit

```text
hat(nu)(a) if a in K^perp, and 0 otherwise.             (FCP4)
```

Fix `x_0 in supp(nu)`.  On `K^perp`, almost-sure constancy says
`hat(nu)(a)=chi_a(x_0)`, so `(FCP4)` is the Fourier transform of Haar measure
on the affine coset `x_0+K`.  This proves `(FCH3)`.

Finally put

```text
K_tilde=closure(span{(x,1):x in supp(nu)}) <= E x F_p.
```

Differences of two generators give `K x {0}`; subtracting `(x_0,1)` shows
that its fiber at `t` is exactly `t x_0+K`.  Haar measure pushes to uniform
measure on the last `F_p` coordinate and has conditional Haar measure on each
fiber.  Shift invariance of the support makes `K_tilde` invariant, while the
last coordinate is fixed.  Hence `q=1_{t=1}` is an invariant projection of
trace `1/p`, central in the crossed product, and

```text
q (L^infinity(K_tilde) rtimes Lambda) q
   = L^infinity(x_0+K,m_(x_0+K)) rtimes Lambda.          (FCP5)
```

This proves the homogenized central-corner statement.

For completeness, a finite affine equation is a character equation
`chi_a(x)=zeta`.  It holds on `supp(nu)` exactly when `a in K^perp`; after
summing `pn+1` samples its constant remains `zeta`, and it holds on
`x_0+K`.  If `a` is not in `K^perp`, its limiting moment is zero.  This proves
the exact affine-preservation statement.
