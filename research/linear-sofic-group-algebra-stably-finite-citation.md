---
rg: 2
id: linear-sofic-group-algebra-stably-finite-citation
kind: route
title: Import Arzhantseva--Paunescu Theorem 7.4 and Proposition 2.8 over an arbitrary field
target: linear-sofic-group-algebra-is-stably-finite
requires: []
---

Source read from the arXiv:1212.6780v1 PDF, 2026-09-11.  Section 2 opens:
"Throughout the article F is an arbitrary field."

> **Theorem 7.4.** Let Θ: G → Π_{k→ω} GL_{n_k}(F)/d_ω be an injective group
> morphism. Then there exists an injective algebra morphism
> Ψ: F(G) → Π_{k→ω} M_{m_k}(F)/Ker ρ_ω.

> **Proposition 2.8.** The algebra Π_{k→ω} M_{n_k}(F)/Ker ρ_ω is stably finite.

Both proofs are characteristic free.

- Theorem 7.4 sums scaled tensor powers `Theta^i` of the representation, so
  `rho(Psi(f)) = sum_i 2^-i rho(Theta^i(f))`.  Injectivity then uses only
  `rho(u (x) v) = rho(u) rho(v)` and invertibility of the images of group
  elements.  The map is unital, since the construction adds an identity block.
- Proposition 2.8 uses `rk(I - ab) = rk(I - ba)`.  Over any field,
  `v -> bv` maps `ker(I - ab)` injectively onto `ker(I - ba)`, because
  `v = abv`.  It also uses `M_m(prod_omega M_n) = prod_omega M_(mn)`.

Their Corollary 7.8 applies exactly this pair to sofic groups over an
arbitrary field, recovering Elek--Szabo.  Stable finiteness passes to the
unital subalgebra `F[G]`.  The field-extension consequence in the target is
immediate, since `K[G] <= L[G]` for `K <= L`.
