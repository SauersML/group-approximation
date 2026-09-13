---
rg: 2
id: thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals
kind: claim
title: A twisted binomial 1 + lambda g of an element of F with dyadic bump endpoints meets every principal right ideal generated inside the pointwise stabilizer of those endpoints
distinct_from:
  thompson-f-multibump-binomials-meet-stabilizer-ideals: that covers b in K[H_i × Z_i], where H_i fixes the closed supports of the other bumps pointwise and may move the endpoints of bump i; this covers b in the pointwise stabilizer of all bump endpoints, which acts independently inside every bump and every fixed interval at once.
  thompson-f-one-bump-binomials-have-common-multiples: that is the one-bump case against every element of K[F]; this is any number of bumps against elements supported in the stabilizer of the bump endpoints, proved by running that claim's count in all bumps simultaneously.
---

**ESTABLISHED (unreviewed).** Let `K` be a field and `R = K[F]`. Let `g ≠ 1` be an
element of `F` whose support has components `I_1 < ... < I_k`, `I_i = (p_i, q_i)`,
with every `p_i` and `q_i` dyadic. Let `W_g` be the subgroup of elements of `F` that
fix every point of `∂_g = {p_1, q_1, ..., p_k, q_k}`.

1. For every `lambda` in `K^x` and every nonzero `b` in `K[W_g]`,
   `(1 + lambda g) R ∩ b R ≠ 0`. The same holds for `b s` with `s` in `F`.
2. *Binomials.* Let `u ≠ w` be in `F`, `alpha, beta` in `K^x`, and `g = w u^-1`. If the
   support components of `g` have dyadic endpoints, then
   `(alpha u + beta w) R ∩ b s R ≠ 0` for every nonzero `b` in `K[W_g]` and every `s`
   in `F`.

**Structure of `W_g`.** List `∂_g ∪ {0, 1}` in increasing order. `W_g` is the direct
product of the groups `F_[z, z']` over consecutive points `z < z'` of that list. These
intervals are the bump closures `[p_i, q_i]` and the nondegenerate fixed intervals of
`g`. So an element of `W_g` acts arbitrarily inside every bump and every fixed interval
at once, provided it fixes the bump endpoints.

**Example.** For two bumps `(0, 1/2)` and `(1/2, 1)`, `W_g = F_[0,1/2] × F_[1/2,1]` is
the stabilizer of `1/2`, and `b` may be any nonzero element of its group ring.
`thompson-f-multibump-binomials-meet-stabilizer-ideals` covers there only `b` in
`K[F_[0,1/2] × <g_2>]` and in `K[<g_1> × F_[1/2,1]]`.

**Consequence for the roots.** Let `(a, b)` be a non-Ore witness for
`thompson-f-is-not-amenable` whose side `a` is a twisted binomial `alpha u + beta w`,
where `g = w u^-1` has dyadic bump endpoints. Then `b` is not a right translate of an
element of `K[W_g]`: for every `s` in `F`, some element of `supp(b s^-1)` moves a bump
endpoint of `g`. With `thompson-f-multibump-binomials-meet-stabilizer-ideals`, the
binomials still open are multi-bump ones against elements that move bump endpoints; see
`thompson-f-every-twisted-binomial-is-ore-with-every-element`.

**Scope.**
- Not covered: `g` with a non-dyadic support endpoint (such as the shared endpoint `1/3`
  in the example of `thompson-f-multibump-binomials-meet-stabilizer-ideals`), and `b`
  that is not a right translate of an element of `K[W_g]`.
- Smaller subgroups do not help: a nonzero element of `(1 + lambda c) R` never lies in
  `K[Stab_F(z)] s` when `c` moves `z` (Remark in the proof route). So the local-to-global
  nesting used for one bump cannot pass between conjugates with different endpoints.
- For `k = 1` this is item 2(b) of `thompson-f-one-bump-binomials-have-common-multiples`
  restricted to `b` fixing `p_1` and `q_1`.
- Novelty: not checked beyond this graph. Web search was unavailable to this lane on
  2026-09-13.
- Review: unreviewed.

Proof route: `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof`.
