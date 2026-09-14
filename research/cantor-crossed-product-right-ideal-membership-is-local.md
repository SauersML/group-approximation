---
rg: 2
id: cantor-crossed-product-right-ideal-membership-is-local
kind: claim
title: In LC(X,F) ⋊ Z for a minimal Cantor system, membership in a principal right ideal aR is a uniformly local column condition in the orbit representations
distinct_from:
  laurent-right-ideals-of-cantor-crossed-products-columnwise: that characterizes qR for a Laurent polynomial q by columns lying in qV, with an explicit division bound; this holds for every a ∈ R, and asks for a local preimage of each column within one uniform radius, with no explicit bound.
  minimal-cantor-crossed-product-is-an-exchange-ring: that asks for the exchange property of the whole ring; this is a membership lemma for principal right ideals, used to test exchange witnesses column by column.
artifacts:
  - research/artifacts/sk-exchange-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, and `R = LC(X,F) ⋊_T Z` with `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`. For `ξ ∈ X` let `V_ξ = F^{(Z)}` carry the orbit representation `fδ_t = f(T^tξ)δ_t`, `uδ_t = δ_{t+1}`.

For `a, z ∈ R` the following are equivalent:
1. `z ∈ aR`;
2. there is `ρ ≥ 0` such that for every `ξ ∈ X` and `t ∈ Z`, `zδ_t ∈ a·span{δ_s : |s−t| ≤ ρ}` in `V_ξ`;
3. for every `ξ ∈ X`, `zδ_0 ∈ a·F^{(Z)}` has a preimage of finite support in `V_ξ`.

**Why it matters.** An idempotent `e ∈ R` witnesses suitability of `a` iff every column of `e` has a local `a`-preimage and every column of `1−e` has a local `(1−a)`-preimage, within one radius. This generalizes the Laurent case, where Laurent division supplies the radius.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part7.md`):** re-derived: covariance V_ξ ≅ V_{T^tξ} and faithfulness; (3⇒2) G_ρ clopen, increasing and covering, then compactness; (2⇒1) one preimage per window type assembled into r = Σ(η_n∘T^{−n})u^n; both one-point model tests.
