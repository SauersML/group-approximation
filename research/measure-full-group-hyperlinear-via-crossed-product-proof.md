---
rg: 2
id: measure-full-group-hyperlinear-via-crossed-product-proof
kind: route
title: Topological full groups embed in the unitary group of the measure crossed product, which transfers Connes embeddability
target: measure-full-group-subgroups-hyperlinear-if-crossed-product-ce
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

Notation as in the target. `lambda_g` are the canonical unitaries of `M`, and `1_U` the projection of a Borel set `U`.
They satisfy `lambda_g 1_U lambda_g^* = 1_(gU)` and `tau(lambda_g f) = δ_(g,e) ∫ f dmu` for `f` in `L^infinity`.

**Step 0 (pieces determine group elements).** Let `U` be a nonempty open set and `g, g'` in `G` with `g x = g' x` for
all `x` in `U`. Then `U ⊆ Fix(g^-1 g')`. Full support gives `mu(U) > 0`, and essential freeness forces `g = g'`.

**Step 1 (well defined).** Two presentations of `gamma` have a common clopen refinement. On a nonempty piece of the
refinement both presentations prescribe elements acting like `gamma`, so by Step 0 they prescribe the same element.
Refining a presentation does not change `Σ_j lambda_(g_j) 1_(U_j)`, because `1_U = Σ 1_(U_i)` for a clopen
partition of `U`. Empty pieces contribute `0`.

**Step 2 (unitary).**
- `u_gamma^* u_gamma = Σ_(j,k) 1_(U_j) lambda_(g_j^-1 g_k) 1_(U_k) = Σ_(j,k) lambda_(g_j^-1 g_k) 1_(g_k^-1 g_j U_j ∩ U_k)`.
  Since `gamma` is injective, `g_j U_j` and `g_k U_k` are disjoint for `j != k`, so those terms vanish. The diagonal
  terms give `Σ_j 1_(U_j) = 1`.
- `u_gamma u_gamma^* = Σ_(j,k) lambda_(g_j) 1_(U_j) 1_(U_k) lambda_(g_k)^* = Σ_j lambda_(g_j) 1_(U_j) lambda_(g_j)^* = Σ_j 1_(g_j U_j) = 1`.
  The cross terms vanish because `U_j ∩ U_k = ∅` for `j != k`, and the last equality holds because `gamma` is onto,
  so the sets `g_j U_j = gamma(U_j)` partition `X`.

**Step 3 (homomorphism).** Let `delta = h_k` on `V_k`. Then
`u_gamma u_delta = Σ_(j,k) lambda_(g_j) 1_(U_j) lambda_(h_k) 1_(V_k) = Σ_(j,k) lambda_(g_j h_k) 1_(h_k^-1 U_j ∩ V_k)`.
The sets `h_k^-1 U_j ∩ V_k` form a clopen partition of `X` on which `gamma delta` equals `alpha(g_j h_k)`, so this is
`u_(gamma delta)` by Step 1.

**Step 4 (trace and injectivity).** `tau(u_gamma) = Σ_(j : g_j = e) mu(U_j)`. Suppose `u_gamma = 1`. Then
`tau(u_gamma) = 1`, so the union of the pieces with `g_j != e` has measure `0`. That union is clopen, and full support
makes it empty. Hence `gamma = id`, and the homomorphism is injective.

**Step 5 (transfer).** Suppose `M` is Connes-embeddable: there is a trace-preserving unital embedding
`theta : M -> R^U` into a tracial matrix ultraproduct. It restricts to an injective group homomorphism
`U(M) -> U(R^U)`. Composing with Steps 1–4 gives an injective homomorphism `[[alpha]] -> U(R^U)`, and restricting to a
subgroup keeps it injective. By condition 1 of `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`
(a countable group is hyperlinear iff it embeds as a subgroup of `U(R^U)`), every countable subgroup of `[[alpha]]`
is hyperlinear. `[[alpha]]` itself is countable, since each element is given by finitely many clopen sets and group
elements.
