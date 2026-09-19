---
rg: 2
id: amenable-basis-coinduction-fence-proof
kind: route
title: Restrict the ambient Fourier expectation to the source coordinate and apply rigidity
target: amenable-basis-coinduction-cannot-create-envelope
requires:
  - haagerup-actor-amenable-basis-rigidity-fence
  - coinduction-retains-crossed-product-not-relation
---

The identity-coset copy of `L(K_0)` is globally invariant under `Gamma`, with
the original automorphism action.  The canonical expectation of
`L(K) rtimes Lambda` kills every nonidentity `Lambda` Fourier coefficient;
restricted to sums over `Gamma` with coefficients in the identity coordinate,
it is exactly the faithful expectation of `L(K_0) rtimes Gamma`.  Hence the
covariant coordinate map is injective and normal, proving `(AGC1)` by the same
calculation as `coinduction-retains-crossed-product-not-relation`.

Because `K_0` is amenable, `L(K_0)` is amenable.  The established Haagerup
amenable-basis rigidity fence says `(AGC1)` contains no property-`(T)`
`II_1` factor, in particular not the fixed `N`.  Coinduction preserves the
faithful source algebra and cannot turn its singular relation quotient into a
normal coordinate inclusion.  This proves the claim without making any
assertion about exotic non-coordinate subalgebras of the full ambient crossed
product.

