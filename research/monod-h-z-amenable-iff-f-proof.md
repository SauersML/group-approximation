---
rg: 2
id: monod-h-z-amenable-iff-f-proof
kind: route
title: Cut the golden hyperbolic element of PSL_2(Z) off at its fixed points, pair it with its unit translate to get a 2-prechain in H(Z), take KKL powers for F inside H(Z), and close with local conjugacy of H(Z) into F
target: monod-h-z-is-amenable-iff-thompson-f-is
requires:
  - kim-koberda-lodha-2-prechain-powers-generate-f
  - integral-piecewise-projective-groups-are-locally-subgroups-of-f
---

**Uses.**
- `kim-koberda-lodha-2-prechain-powers-generate-f`, in its two-generator form. Suppose
  `supp f = (a,b)`, `supp g = (c,d)` with `a < c < b < d`, and `f(t) ≥ t`, `g(t) ≥ t`. Then
  `⟨f^N, g^N⟩ ≅ F` for all sufficiently large `N`.
- `integral-piecewise-projective-groups-are-locally-subgroups-of-f`, Theorem part 4 and C1. Every
  finitely generated subgroup of `G_Z` is conjugate in `Homeo(R)` into `F`, and C1(⇐) says: if `F`
  is amenable, so is every subgroup of `G_Z`.
- Monod's definitions, arXiv:1209.5229, read verbatim at source on 2026-09-20:
  - "Given a subring A < R, we denote by P_A ⊆ P^1 the collection of all fixed points of all
    hyperbolic elements of PSL_2(A)."
  - "We define G(A) to be the subgroup of G given by all elements that are piecewise in PSL_2(A)
    with all interval endpoints in P_A. We write H(A) = G(A) ∩ H, which is the stabilizer of ∞ in
    G(A)."
  - Here `G` is "the group of all homeomorphisms of P^1 which are piecewise in PSL_2(R), each piece
    being an interval of P^1, with finitely many pieces".
  - "Problem 12. Is H(Z) amenable?"

**Step 1 (f and g lie in H(Z)).**
- Let `γ = [[2,1],[1,1]] ∈ SL_2(Z)`, so `γ(t) = (2t+1)/(t+1)`. Its trace is `3 > 2`, so `γ` is
  hyperbolic.
- Its fixed points solve `t^2 - t - 1 = 0`: they are `a = (1-√5)/2` and `b = (1+√5)/2`. So
  `a, b ∈ P_Z`.
- The pole of `γ` is `-1 < a`, and `γ'(t) = (t+1)^{-2} > 0`. So `γ` restricts to an increasing
  homeomorphism of `[a,b]` onto itself, fixing both ends.
- On `P^1`, define `f` by `f = γ` on the arc `[a,b]` (which contains `0`) and `f = id` on the
  complementary arc `[b,a]` (which contains `∞`).
  - The two pieces agree at `a` and `b`, so `f` is a homeomorphism of `P^1`.
  - `f` is piecewise in `PSL_2(Z)` with two interval pieces, whose endpoints `a, b` lie in `P_Z`.
  - `f` fixes `∞`.
  - Hence `f ∈ H(Z)`.
- Let `τ = [[1,1],[0,1]]`, so `τ(t) = t+1`. Put `δ = τγτ^{-1} = [[3,-1],[1,0]]`, with trace `3`.
  - Its fixed points are `a+1 = (3-√5)/2` and `b+1 = (3+√5)/2`, which lie in `P_Z`.
  - Its pole is `0 < a+1`.
  - The map `g = τfτ^{-1}` is `δ` on `[a+1,b+1]` and `id` elsewhere.
  - By the same argument, `g ∈ H(Z)`.

**Step 2 (one-bump, moving right).**
- `γ(t) - t = -(t^2 - t - 1)/(t+1)`. On `(a,b)` the numerator `t^2 - t - 1` is negative and
  `t + 1 > 0`, so `γ(t) > t` there.
- Hence `supp f = (a,b)`, and `f(t) ≥ t` for all real `t`.
- Likewise `δ(t) - t = -(t^2 - 3t + 1)/t > 0` on `(a+1,b+1)`, so `supp g = (a+1,b+1)` and
  `g(t) ≥ t`.

**Step 3 (2-chain; F inside H(Z)).**
- `b - a = √5 > 1`, so `a < a+1 < b < b+1`.
- The supports form a 2-chain of intervals with `∂^-J_1 = a < a+1 = ∂^-J_2`. Their intersection
  `(a+1,b)` is a proper nonempty subinterval of each.
- By `kim-koberda-lodha-2-prechain-powers-generate-f`, `⟨f^N, g^N⟩ ≅ F` for all sufficiently large
  `N`. Fix one such `N`. Then `F ≅ Φ_N := ⟨f^N, g^N⟩ ≤ H(Z)`.
- `golden_prechain_check.py` checks Steps 1–3 in exact arithmetic over `Q(√5)`.

**Step 4 (H(Z) inside G_Z).**
- An element `h ∈ H(Z)` fixes `∞`. Its pieces are in `PSL_2(R)`, which preserves the orientation of
  `P^1`.
- So `h` restricts to an increasing homeomorphism of `R = P^1 \ {∞}`.
- Off the finitely many piece endpoints, `h|_R` agrees on each complementary interval with an element
  of `PSL_2(Z)`. The piece containing `∞` becomes two unbounded intervals of `R`, both carrying the
  same element.
- So `h|_R ∈ G_Z`. Since `h ↦ h|_R` is an injective homomorphism, `H(Z) ≤ G_Z`.

**Step 5 (equivalence).** Let `𝒫` be a property of groups that passes to subgroups and to directed
unions of countable groups. Amenability is such a property. Let `Φ_N ≤ Γ ≤ G_Z`. For example,
`Γ = H(Z)` by Steps 3 and 4.
- **(⇒)** If `Γ` has `𝒫`, so does its subgroup `Φ_N ≅ F`.
- **(⇐)** Suppose `F` has `𝒫`.
  - By part 4 of `integral-piecewise-projective-groups-are-locally-subgroups-of-f`, every finitely
    generated `H ≤ Γ ≤ G_Z` is conjugate in `Homeo(R)` to a subgroup of `F`. In particular it is
    isomorphic to one, so it has `𝒫`.
  - `Γ` is countable, because `G_Z` is. So `Γ` is the directed union of its finitely generated
    subgroups, and `Γ` has `𝒫`.
- For amenability, (⇐) is exactly C1(⇐) of that node.
- Taking `Γ = H(Z)` and `𝒫 = amenability` gives parts 2 and 3 of the claim. ∎

**What is imported and what is not.**
- KKL Theorem 1.1 is imported verbatim; its proof is not re-derived.
- Local conjugacy into `F` is an established lane proof in this graph, not reviewed.
- Monod's definitions and Problem 12 were read at source.
- Nothing else is used.
