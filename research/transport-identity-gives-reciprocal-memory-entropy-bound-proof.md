---
rg: 2
id: transport-identity-gives-reciprocal-memory-entropy-bound-proof
kind: route
title: Bound each of the |N| transport terms by the site entropy and divide
target: transport-identity-gives-reciprocal-memory-entropy-bound
requires:
  - injective-ca-random-order-transport-identity
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
---

Artifact Section 1, Proposition 1.

Let `y = kappa(x)`, `x` uniform, `U` the i.i.d. order labels independent of `x`. For `n in N` put
`A_n = E_U I( x(n^-1) ; y(e) | Z_n, U )` with `Z_n = y(n^-1 N ∩ past(e))`.

1. For every fixed realization of `U`, `I( x(n^-1) ; y(e) | Z_n ) <= H( y(e) | Z_n ) <= H( y(e) )`, since
   conditional mutual information is at most the conditional entropy of either argument, and conditioning does not
   increase entropy.
2. `H(y(e))` is independent of `U` (the labels `U` are independent of `(x, y)`), so averaging step 1 over `U` gives
   `A_n <= H(y(e))` for each `n in N`.
3. `injective-ca-random-order-transport-identity` gives `sum_(n in N) A_n = log |A|`.
4. Summing step 2 over the `|N|` terms and using step 3: `log |A| = sum_n A_n <= |N| · H(y(e))`, so
   `H(y(e)) >= (log |A|) / |N|`.

The per-term bound in step 1 is attained (artifact `random-order-decoder-transport` 2.5: a bijective automaton on `Z`
has one transport term equal to the full site entropy), so no term-by-term argument improves the constant `1/|N|`.
