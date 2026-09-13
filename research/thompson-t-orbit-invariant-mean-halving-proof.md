---
rg: 2
id: thompson-t-orbit-invariant-mean-halving-proof
kind: route
title: Halve the half-circle with x_0, double it back with a rotation
target: thompson-t-orbits-carry-no-invariant-means
requires: []
---

All intervals are half-open arcs `[a,b)` of `S^1 = R/Z`. The three elements `r_(1/4)`,
`r_(1/2)`, `x_0` are increasing homeomorphisms of the circle, so each maps a half-open arc
onto a half-open arc: `x_0[0,1/2) = [0,1/4)`, `r_(1/4)[0,1/4) = [1/4,1/2)`, and
`r_(1/2)[0,1/2) = [1/2,1)`.

**Step 1: word lengths control displacement.** For a finite `F` put
`eps = max_(s in X) |sF Δ F| / |F|`. Each `s` is a bijection of `S^1`, so
`|s^(-1)F Δ F| = |s^(-1)(F Δ sF)| = |F Δ sF|`, and `X` is symmetric anyway. For a word
`g = s_1 ... s_k`, the triangle inequality for symmetric differences along the prefixes,
together with `|s(A Δ B)| = |A Δ B|`, gives `|gF Δ F| <= k eps |F|`. So `|gF Δ F| <= L eps |F|`
for `g` in `{x_0, r_(1/4), r_(1/2)}`.

**Step 2: approximate invariance of the counting measure.** Put `mu(A) = |A ∩ F| / |F|`
for arcs `A`. This is finitely additive on disjoint arcs, with `mu(S^1) = 1`. For any `g`,
```text
|gA ∩ F| = |A ∩ g^(-1)F|,   and   | |A ∩ g^(-1)F| - |A ∩ F| | <= |g^(-1)F Δ F| = |F Δ gF|.
```
So `|mu(gA) - mu(A)| <= L eps` for each of the three elements.

**Step 3: halving.** Let `a = mu[0,1/4)`, `b = mu[1/4,1/2)` and `h = mu[0,1/2) = a + b`.
- From `x_0`: `|h - a| <= L eps`, so `b <= L eps`.
- From `r_(1/4)`: `|b - a| <= L eps`, so `a <= 2 L eps` and `h <= 3 L eps`.
- From `r_(1/2)`: `mu[1/2,1) <= h + L eps <= 4 L eps`.

Hence `1 = mu[0,1/2) + mu[1/2,1) <= 7 L eps`, which is (TC1).

**Consequences in item 1.** A connected bounded-degree graph with a positive isoperimetric
constant has no Følner sets, and (TC1) bounds the constant uniformly over every finite
point set, in one orbit or several. A truncation of the action to `F`, corrected on
`o(|F|)` points, would give `|sF Δ F| = o(|F|)` for every `s`, contradicting (TC1).

**Item 2, measures.** If `nu` is a Borel probability measure invariant under the three
elements, run Step 3 with `nu` in place of `mu` and `eps = 0`. The images of half-open arcs
are half-open arcs, so invariance is exact: `nu[0,1/2) = nu[0,1/4)`,
`nu[1/4,1/2) = nu[0,1/4)`, so `nu[0,1/4) = 0`, then `nu[0,1/2) = 0`, then
`nu[1/2,1) = nu[0,1/2) = 0`, and `nu(S^1) = 0`. That is a contradiction.

**Item 2, covariant representations.** Suppose `P_k` are nonzero finite-rank projections with
`delta_k(g) = ||pi(g) P_k pi(g)^* - P_k||_HS / ||P_k||_HS -> 0` for `g` in `X`. Define states
`Phi_k(x) = Tr(P_k x) / Tr(P_k)` on `B(H)`.
- **Trace-norm estimate.** Put `Y = pi(g) P_k pi(g)^* - P_k`. Its rank is at most `2 rank(P_k)`, so
  ```text
  ||Y||_1  <=  sqrt(2 rank P_k) ||Y||_HS  =  sqrt(2) ||P_k||_HS delta_k(g) ||P_k||_HS
          =  sqrt(2) delta_k(g) Tr(P_k),
  ```
  using `||P_k||_HS^2 = Tr(P_k) = rank(P_k)`.
- **Approximate invariance.** `|Phi_k(pi(g)^* x pi(g)) - Phi_k(x)| = |Tr(Y x)| / Tr(P_k) <= sqrt(2) delta_k(g) ||x||`.
- **Limit.** A weak-* cluster point `Phi` of `(Phi_k)` is a state invariant under
  `Ad pi(g)` for `g` in `X`, hence under the generated group. So `Phi o rho` is a state
  on `C(S^1)`, invariant under composition with the three elements by covariance.
  Riesz gives an invariant Borel probability measure, contradicting the previous paragraph.
