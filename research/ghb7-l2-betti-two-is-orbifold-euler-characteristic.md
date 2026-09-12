---
rg: 2
id: ghb7-l2-betti-two-is-orbifold-euler-characteristic
kind: claim
title: The second L2-Betti number of GHB_2(7) is 1381/2401, so its congruence kernel has nonzero degree-two L2-cohomology
distinct_from:
  ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2: that computes the ordinary rational b_2 of the kernel H from the Euler characteristic; this computes the L2-Betti numbers of H and of GHB_2(7) and records that degree-two cohomology with coefficients in the regular representation is nonzero
  free-cocompact-lattices-proportional-l2-betti: that is a proportionality principle between two groups acting freely and cocompactly on one complex; this is an explicit value for one group through the Atiyah Euler characteristic formula and property (T)
---

**ESTABLISHED** by [[ghb7-l2-betti-two-euler-proof]].

Let `G = G_{HB_2}(7)`, let `ψ` be the CCKW quotient map to `SL_4(F_7)`, and let
`H = Ker ψ`, as in `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`. Then

```text
b_0^(2)(H) = b_1^(2)(H) = 0,
b_2^(2)(H) = χ(H) = [G:H] · 1381/2401,
b_k^(2)(H) = 0 for k >= 3,

b_2^(2)(G) = 1381/2401,   b_k^(2)(G) = 0 for k != 2.
```

In particular the reduced cohomology `H̄^2(H; ℓ²H)` is nonzero, and so is the
unreduced cohomology `H^2(H; ℓ²H)`, of which it is a quotient.

**Consistency check.** By CCKW Theorem 3.1(ii) every finite subgroup of `G` is
conjugate into a vertex group, of order `343` or `2401`. So the Atiyah conjecture for
groups with torsion allows denominators dividing `2401`, and `1381/2401` fits.

**What it is used for.** Positive `b_2^(2)` is the input of
`ghb7-kernel-blocks-degree-two-newton-stability`: degree-two cohomology vanishing on
regular coefficients is false for `H`, so it cannot be the source of flexible
Hilbert--Schmidt stability of `H`.
