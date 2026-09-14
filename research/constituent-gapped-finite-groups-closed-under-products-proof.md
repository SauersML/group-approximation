---
rg: 2
id: constituent-gapped-finite-groups-closed-under-products-proof
kind: route
title: Irreducible representations of products are tensor products, a tensor product is scalar only when both factors are, and quotients keep their characters
target: constituent-gapped-finite-groups-closed-under-products
requires: [lst-quasisimple-classical-character-ratio-bound]
---

**(a) Products.**
- The irreducible complex representations of `A × B` are exactly the `σ ⊗ τ` with `σ`, `τ` irreducible, and
  `χ̃_{σ⊗τ}(a,b) = χ̃_σ(a) χ̃_τ(b)` (standard character theory of direct products).
- If `σ(a) = λI` and `τ(b) = μI`, then `σ(a) ⊗ τ(b) = λμ I`. So if `(σ⊗τ)(a,b)` is not a scalar, one of `σ(a)`, `τ(b)` is not
  a scalar. That factor has ratio at most `θ` in absolute value, and the other at most `1`. So `|χ̃_{σ⊗τ}(a,b)| ≤ θ`.
- Induct on the number of factors.

**(a) Quotients.** An irreducible representation of `Q/K` is an irreducible representation `σ∘π` of `Q` with the same character
values. If `σ(π(q))` is not a scalar, its ratio is at most `θ` by the hypothesis on `Q`.

**(b) Abelian groups.** Their irreducible representations are one-dimensional, so every `σ(q)` is a scalar and the condition is
vacuous.

**(c) Quasisimple classical groups.** Let `Γ` be one, and `σ` irreducible.
- If `σ` is trivial, every `σ(q)` is a scalar.
- If `σ` is nontrivial and `σ(q)` is not a scalar, then `q ∉ Z(Γ)`, because central elements act by scalars in irreducible
  representations (Schur). By `lst-quasisimple-classical-character-ratio-bound`, `|χ̃_σ(q)| < 2^{−1/481}`.

**(d) Groupwise gaps.** Suppose `|χ(q)| ≤ θ χ(1)` for every nontrivial irreducible `χ` and every noncentral `q`. If `σ(q)` is
not a scalar, then `σ` is nontrivial and `q` is noncentral (Schur), so the ratio is at most `θ`.
The converse fails: in `A × B` with `B` nonabelian, the representation `σ ⊗ 1` has ratio `1` at `(1,b)` for noncentral `b`.

**(e) Subgroups.** `A_m` embeds in `SL_m(F_q)` by even permutation matrices, which have determinant `1`.
- For `m ≥ 4` the standard representation of `A_m` (the permutation module minus the trivial one) is irreducible of dimension
  `m − 1`.
- A 3-cycle acts non-scalarly, with character value `m − 4`, so its ratio is `(m−4)/(m−1) → 1`. ∎
