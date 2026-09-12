---
rg: 2
id: necklace-realizable-measures-can-violate-serre
kind: claim
title: A positive measure whose nonnegative integral matrix images all have realizable moment sequences can violate the Serre inequality
distinct_from:
  euler-integral-measure-violates-serre-inequality: that shows the same measure has integer Euler products for every integral polynomial image, a condition closed under integer differences; this shows it also passes the positivity-aware test, nonnegative necklace counts for every nonnegative integral matrix image, which is not closed under differences
  torsion-free-integral-zeta-is-an-integer-euler-product: that is the signed necklace expansion valid for every integral matrix over a torsion-free group; this is the nonnegative refinement for nonnegative matrices and a measure satisfying it that violates the Serre inequality
---

**ESTABLISHED** by `necklace-realizable-serre-violation-proof`.

**Realizability.** A sequence `(N_j)_(j>=1)` of integers is *realizable* if
the necklace numbers

```text
p_d = (1/d) * sum_(e | d) mobius(d/e) * N_e
```

are nonnegative integers for every `d >= 1`. Equivalently
`exp( sum_(j>=1) N_j z^j / j ) = prod_(d>=1) (1 - z^d)^(-p_d)` with `p_d >= 0`.
These are exactly the periodic-point counts of maps (Puri--Ward). Unlike
integrality of moments or of Euler products, the realizable sequences form a
cone: they are closed under sums but not under differences.

**The positivity-aware class.** Call a compactly supported positive Borel
measure `mu` on `R` *necklace realizable* if for every `k >= 1` and every
`P in M_k(Z_(>=0)[x])` the sequence `N_j = integral Tr(P(x)^j) d mu(x)` is
realizable. Over a torsion-free group, the spectral measure of every
self-adjoint `T in M_n(Z_(>=0)[G])` is necklace realizable (step 1 of the
proof). The moment functional of any positive measure is also completely
positive: `integral P(x)^* P(x) d mu >= 0` for all `P in M_k(C[x])`.

**Claim.** Let `nu`, `sigma` and `mu = 23 nu - sigma` be the `Z^3` measures of
`euler-integral-measure-violates-serre-inequality`:
- `nu` is the law of `(g+g^-1)(h+h^-1)(k+k^-1)`;
- `sigma` is the law of `g+g^-1+h+h^-1+k+k^-1`.

Then `mu` is necklace realizable, its moment functional is completely positive,
and `integral_(x != 0) log|x| d mu < 0`. So the necklace-realizable class is not
contained in the Serre class.

**Consequence.** The positivity-aware moment classes suggested by the
Euler-integral refutation do not exclude its counterexample:
- nonnegative necklace counts of all nonnegative integral matrix images;
- complete positivity of the moment functional.
Positivity at the level of moments survives dominated differences: here
`sigma`'s letters inject into `nu`'s letters through an injective endomorphism
of `Z^3`, so every necklace count of `sigma` is at most the corresponding count
of `nu`. An approximation-free proof of the determinant conjecture therefore
has to use more than the moment sequences of nonnegative integral images of a
single operator. Realizability of the measure as the spectral measure of an
operator, with its multiplicative structure, is still untested.

**What it does not show.** The determinant conjecture is untouched, `mu` is not
the spectral measure of any group-ring element, and signed matrix images of
`mu` are not claimed realizable. Spectral measures of signed elements need not
be realizable either: `T = -1` gives `N_1 = -1`.
