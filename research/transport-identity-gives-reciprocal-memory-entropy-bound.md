---
rg: 2
id: transport-identity-gives-reciprocal-memory-entropy-bound
kind: claim
title: The single-site output entropy of an injective automaton is at least log |A| over its left-inverse memory size
distinct_from:
  injective-ca-images-have-full-single-site-entropy: that asks for the full bound log |A|, which is equivalent to the goal; this is the elementary bound (log |A|)/|N| from subadditivity, which is also all that the random-order transport identity gives when each term is bounded by the site entropy.
  decoder-window-fiber-bound-loses-exactly-the-boundary: that is a per-window counting bound losing the right boundary on nonamenable groups; this is a single-site entropy bound valid over every group with no counting.
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---

**ESTABLISHED** by `transport-identity-gives-reciprocal-memory-entropy-bound-proof`.

Let `G` be any group, `A`, `B` finite alphabets, and `kappa : A^G -> B^G` an injective automaton with a left inverse
of memory `N` containing `e`. Under the uniform product measure on `A^G`,

    H( kappa(x)(e) )  >=  (1 / |N|) log |A| .

The proof is subadditivity: `x(e)` is a function of `y|_N`, so `log |A| <= H(y|_N) <= |N| H(y(e))`. Despite the id, the
bound needs no transport. Its role here is calibration: bounding each term of
`injective-ca-random-order-transport-identity` by `H(y(e))` and summing reproduces exactly this bound. So the identity
adds nothing at that level, and domination (`injective-ca-random-order-transport-is-dominated`, the constant-`1`
case, equivalent to the goal) needs the conditionings used jointly.

## Attempts
- **Sharpness not claimed.** Over amenable groups every injective automaton already has `H(y(e)) >= log |A|`. An
  earlier version said the per-term bound is attained and no term-by-term argument beats `1/|N|`. That is withdrawn:
  attainment holds only for one order realization in the `Z` example, and the average there is `3/2 < 2`.
- **Sharper per-term form.** `A_n <= H(y(e) | Z_n, U)` gives `sum_n H(y(e) | Z_n, U) >= log |A|`. That is not
  domination, because the conditionings differ. See `three-point-decoder-memory-injective-ca-are-surjective`.
