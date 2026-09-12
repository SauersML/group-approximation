---
rg: 2
id: kk-half-mass-measures-pass-arithmetic-at-every-capacity
kind: claim
title: Integer moments, zeta integrality and any capacity bound are consistent with spectral components of mass one half
distinct_from:
  integral-spectra-of-small-capacity-are-finite: that forces finite spectrum below capacity one; this shows that above capacity one the same arithmetic data cannot force integer component masses, at every capacity.
  small-capacity-kk-witnesses-are-algebraic-idempotents: that locates small-capacity witnesses among algebraic idempotents; this shows the capacity lower bound it derives for analytic witnesses is no obstruction to non-integer masses.
  torsion-free-integral-zeta-is-an-integer-euler-product: that proves zeta integrality over torsion-free groups; this shows zeta integrality, moment integrality and large capacity together still allow two components of mass one half.
  reduced-projection-iff-gapped-spectral-measure: that reformulates reduced projections as gapped integral spectral measures; this is a fence on proofs of integrality that use only the arithmetic of such measures.
---

**ESTABLISHED** by `kk-half-mass-arithmetic-capacity-proof`.

Let `u` generate `Z` and `g` generate `Z/2`, and for an integer `N >= 3` put

```text
Y = N + u + u^(-1)  in Z[Z],        T_N = 2 Y g  in Z[Z x Z/2].
```

Then `T_N` is self-adjoint, and its spectral measure `mu_N` for the canonical
trace has all of the following properties.

1. **Gapped support:** `sigma(T_N) = [-2N-4, -2N+4] ⊔ [2N-4, 2N+4]`, with the gap
   `(-2N+4, 2N-4)` around `0`.
2. **Half masses:** each component carries mass `1/2`, since
   `mu_N = (mu_(2Y) + mu_(-2Y))/2`.
3. **Integer moments:** `tau(T_N^j) = tau((2Y)^j)` for even `j`, and `0` for odd `j`.
4. **Zeta integrality:** `exp(sum_j tau(T_N^j) z^j / j)` lies in `Z[[z]]`, so every
   necklace (ghost) congruence `sum_(d | n) mu(n/d) tau(T_N^d) ≡ 0 (mod n)` holds.
5. **Large capacity:** `cap(sigma(T_N)) = sqrt(8N)`, which is at least `1` and tends to
   infinity.

**Consequence (a fence).** Take the arithmetic facts that main proves for integral
self-adjoint elements over torsion-free groups: integer moments, integrality of the
zeta Euler product, and positivity. Together with any lower bound on spectral
capacity, they cannot force integer masses on spectral components. The recorded
two-atom example `(delta_2 + delta_(-2))/2` already did this at capacity `0`; this
family does it at every capacity.

So the dichotomy in `small-capacity-kk-witnesses-are-algebraic-idempotents` is sharp
and carries no further arithmetic content. A witness in `Z[i][G]` either has finite
spectrum, hence algebraic spectral projections, or has spectrum of capacity at least
`1`, and nothing in the moment and zeta arithmetic alone excludes the second case.

A proof of Kadison--Kaplansky, or of trace integrality, must use torsion-freeness of
`G` through the algebra: assembly or index theory, as in the Kaad--Proietti mechanism
recorded on `kadison-kaplansky-torsion-free`. Spectral-measure arithmetic is not
enough, because `T_N` lives over a group with 2-torsion while passing every one of
these tests.

**Scope.** This is not a counterexample to anything. `Z x Z/2` has torsion, and since
`Y` is positive and invertible, `chi_((0,inf))(T_N)` is exactly the torsion projection
`(1+g)/2`. Only the measure-level consistency is asserted.
