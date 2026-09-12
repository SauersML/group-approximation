---
rg: 2
id: euler-integral-measure-violates-serre-inequality
kind: claim
title: A positive measure whose integral polynomial images all have integer moment Euler products can violate the Serre inequality
invalidates:
  - master-host-determinant-via-euler-integrality
distinct_from:
  euler-integral-measures-are-serre-class: that is the universal arithmetic criterion; this is an explicit counterexample to it, a Z-linear combination of two spectral measures over Z^3
  integer-moment-measure-with-negative-log-determinant: that measure has integer moments but fails Euler integrality at p = 2; this one has integer Euler products for every integral polynomial image
---

**ESTABLISHED** by `euler-integral-serre-counterexample-proof`.

Let `X, Y, Z` be independent, each with the arcsine law on `[-2,2]`. Put

```text
nu    = law(X Y Z)      spectral measure of (g+g^-1)(h+h^-1)(k+k^-1) in Z[Z^3]
sigma = law(X + Y + Z)  spectral measure of g+g^-1+h+h^-1+k+k^-1    in Z[Z^3]
mu    = 23 nu - sigma
```

Then:

- `mu` is a positive Borel measure of mass `22` on `[-8,8]`.
- For every `Q in Z[x]` the moments `integral Q^j d mu` are integers, and
  `exp( sum_(j>=1) integral Q^j d mu z^j / j )` lies in `1 + z Z[[z]]`.
- `integral_(x != 0) log|x| d mu = - m(x + 1/x + y + 1/y + z + 1/z) < 0`.

So `euler-integral-measures-are-serre-class` is false. The route
`master-host-determinant-via-euler-integrality` is dead.

**Why it fails.** The hypothesis, Euler integrality of every polynomial image,
is closed under Z-linear combinations of measures. The Serre inequality is only
preserved under positive combinations. Subtracting a spectrum of positive
Mahler measure from a dominating multiple of a spectrum of Mahler measure zero
keeps the first property and destroys the second.

**What it does not show.** `mu` is not claimed to be the spectral measure of any
group-ring element, and `Z^3` satisfies the determinant conjecture. The
determinant conjecture itself is untouched. What dies is every approximation-free
proof that uses only moment congruences of single operators. Such a proof must
also use realizability of the spectral measure, or complete positivity across
integral matrix images, not just integrality of one-variable moments.
