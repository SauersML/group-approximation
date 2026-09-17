---
rg: 2
id: weakly-minimal-oe-transfers-rokhlin-supremum-proof
kind: route
title: Compare both groups' Bernoulli entropies through the shared relation value, then pass to the product with the dyadic odometer
target: weakly-minimal-oe-transfers-rokhlin-supremum
requires:
  - bernoulli-rokhlin-entropy-is-an-orbit-relation-invariant
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - positive-rokhlin-entropy-action-gives-positive-supremum
artifacts:
  - research/artifacts/bernoulli-bundle-orbit-relation-entropy-2026-09-17.md
---

The details are Corollaries A3 and A4 in the artifact. `E_λ(R)` is the orbit-relation value from
`bernoulli-rokhlin-entropy-is-an-orbit-relation-invariant`.

**Items 1 and 2.** Let Y be weakly minimal free for G and orbit equivalent to a free Γ-action W. For
`H(λ) < ∞`, item 2 of the invariance claim, then its item 1, then its item 3 give

    h^Rok_G(L^G) = E_λ(R_Y) = E_λ(R_W) <= h^Rok_Γ(L^Γ).

By Seward's Theorem 1.10 (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, item 1, verbatim:
"h^Rok_G(L^G,λ^G) = min{H(L,λ), h^Rok_sup(G)}"), this reads

    min{H(λ), h_sup(G)} <= min{H(λ), h_sup(Γ)}   for every H(λ) ∈ (0, ∞).

Hence `h_sup(G) <= h_sup(Γ)`. If W is weakly minimal, item 2 of the invariance claim for Γ turns the
inequality into an equality. The group properties translate as follows:

* INF is `h_sup = ∞` by definition.
* RBS ⇒ INF, since `min{H, h_sup} = H` for all finite H forces `h_sup = ∞`. INF ⇒ RBS is Seward's.
* POS ⇔ `h_sup > 0` is `positive-rokhlin-entropy-action-gives-positive-supremum`.

**Item 3.** Let `P = ⊕_N Z/2` act freely by translation on `Z = (Z/2)^N` with Haar measure. Its orbit
relation is R_0. The action `G × P ↷ Y × Z` is free, with orbit relation `R_Y × R_0 ≅ R_Y`. By the
invariance claim (items 2, 1, 3),

    min{H(λ), h_sup(G)} = E_λ(R_Y) = E_λ(R_Y × R_0) <= h^Rok_{G×P}(L^{G×P}) = min{H(λ), h_sup(G × P)}.

Suppose `h_sup(G) < ∞`. Seward's Theorem 1.11 (same node, item 3, verbatim: "If G is any countably infinite
group with h^Rok_sup(G) < ∞ then h^Rok_sup(P × G) = 0") applies, since P contains arbitrarily large finite
subgroups. So the right side is 0 for every λ, which forces `h_sup(G) = 0`. So `h_sup(G) ∈ {0, ∞}`.
