---
rg: 2
id: gl-infinity-f2-extreme-characters-are-rank-powers
kind: claim
title: The extreme characters of GL(infinity,2) are exactly the rank powers 2^(-k rank(g-1)), k = 0,1,...,infinity
distinct_from:
  dlv-locally-inner-inducing-character-classification: that imports only the countability of Ch(GL(infinity,q)) and the rank decay of nontrivial characters of SL_fin(F_q); this imports the explicit list.
  jacobson-el-characters-are-symbol-or-finitary-extensions: that reduces the characters of EL_n(J) off the symbol to Ch(L) minus {1}; this names every element of Ch(L).
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that constructs the Haar fixed-point characters phi_k and observes that they are rank powers on L; this says that the rank powers are all the characters of L.
---

**ESTABLISHED by citation**
([[gl-infinity-f2-extreme-characters-are-rank-powers-citation]]).

**Statement.**
* `GL(∞,q)` is the inductive limit of `GL(n,q)` under the corner embeddings.
* A trace is a normalized, positive-definite, conjugation-invariant function. A character is an extreme
  trace (conventions of `dlv-locally-inner-inducing-character-classification`).
* The characters of `GL(∞,q)` are exactly `g ↦ ε(det g) q^(−m·rank(g−1))`, where `m ∈ {0,1,2,...,∞}` and
  `ε` is a character of `F_q^*`. The case `m = ∞` means `δ_e`.
* **For `q = 2`.** The characters are exactly

```text
sigma_m(g) = 2^(-m rank(g-1)),      m = 0, 1, 2, ..., infinity,
```

  with `sigma_0 = 1` and `sigma_infinity = delta_e`.

**Any countable index set.** Take any countably infinite index set `I`, for example `N x {1..n}`.
Enumerating `I` makes `GL_fin(I, F_2)` the corner inductive limit, so `GL_fin(I, F_2) ≅ GL(∞,2)` and the
same list applies. The consequences for `EL_n(J)` are drawn in
`gl-infinity-f2-trace-simplex-is-extended-naturals`.

**Consistency check.** For `m >= 1` the value `sigma_m(g) → 0` as `rank(g−1) → ∞`. This is Proposition 8.5
of Dogon--Levit--Vigdorovich (rank decay), as imported in `dlv-locally-inner-inducing-character-classification`.
