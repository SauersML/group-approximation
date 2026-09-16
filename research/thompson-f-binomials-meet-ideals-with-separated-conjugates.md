---
rg: 2
id: thompson-f-binomials-meet-ideals-with-separated-conjugates
kind: claim
title: A twisted binomial 1 + lambda g in K[F] meets b R whenever the conjugates of g by the support of b keep their bumps between common dyadic separating points
distinct_from:
  thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals: that covers b in the pointwise stabilizer of every bump endpoint of g, so all conjugates of g by supp b have the same bumps; this lets supp b move every bump endpoint at once, as long as the conjugated bumps of each index stay between common dyadic separating points, and contains that claim as the case of coinciding bumps.
  thompson-f-multibump-binomials-meet-stabilizer-ideals: that covers b in K[H_i × Z_i], whose elements move the endpoints of the single bump i; this moves the endpoints of all bumps simultaneously and contains that claim.
  thompson-f-every-twisted-binomial-is-ore-with-every-element: that asks for every b; this settles the b with separated conjugates, and leaves exactly the b whose conjugated bumps cross.
---

**ESTABLISHED (unreviewed).** Let `K` be a field and `R = K[F]`. Composition is right to
left, so `t^-1 g t` has support `t^-1(supp g)`.

**Definition.** Let `g ≠ 1` be in `F` with support components `I_1 < ... < I_k`,
`I_i = (p_i, q_i)`. A finite set `T ⊆ F` is *`g`-separated* if there are dyadic numbers
`0 = z_0 < z_1 < ... < z_(k-1) < z_k = 1` with `t^-1(I_i) ⊆ (z_(i-1), z_i)` for every `t`
in `T` and every `i`. Equivalently, for every `i < k`,
`max_(t in T) t^-1(q_i) <= min_(t in T) t^-1(p_(i+1))`, and `q_i` is dyadic if
`q_i = p_(i+1)`.

For dyadic `Z = {z_1 < ... < z_(k-1)}` let `V_Z` be the pointwise stabilizer of `Z` in
`F`, so `V_Z = F_[z_0,z_1] × ... × F_[z_(k-1),z_k]`. Call `c` in `V_Z` *Z-one-bump* if its
restriction to every `[z_(i-1), z_i]` is one-bump.

1. **Families.** For Z-one-bump `c^(1), ..., c^(r)` and `lambda_1, ..., lambda_r` in `K^x`,
   `∩_j (1 + lambda_j c^(j)) K[V_Z] ≠ 0`, hence `∩_j (1 + lambda_j c^(j)) R ≠ 0`.
2. **Separated supports.** For `g ≠ 1`, `lambda` in `K^x` and nonzero `b` in `R` with
   `supp b` `g`-separated, `(1 + lambda g) R ∩ b R ≠ 0`.
3. **Binomials.** For `u ≠ w` in `F`, `alpha, beta` in `K^x` and `g = w u^-1`,
   `(alpha u + beta w) R ∩ b R ≠ 0` for every nonzero `b` with `supp b` `g`-separated.

**Special cases.** Separation is invariant under `T -> T s` (use `s^-1(Z)`).
- `b` in `K[W_g] s`, bump endpoints dyadic: take `z_i = q_i`. This is
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals`.
- `b` in `K[H_i × Z_i] s` (the factors of `g` in `F`): take `z_(i-1) = q_(i-1)`,
  `z_i = p_(i+1)` and `z_j = q_j` otherwise. This is
  `thompson-f-multibump-binomials-meet-stabilizer-ideals`.
- `b` in `K[V_Z] s` for any dyadic `Z` with `q_i <= z_i <= p_(i+1)` for every `i < k`.
  For two bumps sharing a dyadic endpoint `m`, `z_1 = m` is forced, `V_Z = Stab_F(m)`, and
  `b` may be any element of `K[Stab_F(m)] s`.

**Example beyond both earlier claims.** Let `g` have bumps `(1/8, 1/2)` and `(1/2, 7/8)`,
and `b = 1 + t + t^2` with `t` in `Stab_F(1/2)` moving both `1/8` and `7/8`. The support
`{1, t, t^2}` has three elements because `F` is torsion-free, and it is `g`-separated by
`z_1 = 1/2`.
- `supp b` lies in no translate `W_g s`, because then `t = t · 1^-1` would lie in `W_g`.
- If `supp b ⊆ (H_i × Z_i) s`, then `t` lies in the group `H_i × Z_i`, whose elements fix
  the endpoints of the bump other than `i`; but `t` moves `1/8` and `7/8`.
- Item 3 of `thompson-f-binomial-pairs-have-common-multiples` needs `|supp b| <= 2`.

**Consequence for the roots.** Let `(1 + lambda g, b)` be a non-Ore pair in `K[F]`. Then
some `i < k` and `t, t'` in `supp b` have `t^-1(q_i) > t'^-1(p_(i+1))`, or `g` has a
non-dyadic shared endpoint. So a counterexample to
`thompson-f-every-twisted-binomial-is-ore-with-every-element`, and a binomial-sided
non-Ore witness for `thompson-f-is-not-amenable`, needs two conjugates of `g` by elements of
`supp b` such that bump `i` of one ends to the right of the start of bump `i + 1` of the
other.

**Scope.**
- Not covered: non-dyadic shared endpoints, and `b` that is not separated, such as
  `g` with bumps `(0, 1/4)`, `(3/4, 1)` and `b = 1 + t` with `t^-1(1/4) > 3/4`.
- Proof: the base case is item 1 of
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals`, restricted to
  `K[F_[a_1,d_1] ... F_[a_k,d_k]]`. On top of it sits a nesting by hulls that releases the
  `2k` endpoint coordinates one at a time. With `k = 1` the nesting is Lemma D plus Item 1
  of `thompson-f-rescaled-x0-binomials-have-common-multiples-proof`.
- Novelty: not checked beyond this graph. Searches on 2026-09-16 found no source on the
  Ore condition for multi-bump binomials in `K[F]`
  (`notes/zaremsky-2-01-thompson-f-amenable-special-case-swarm-2026-09-16.md` §1).
- Review: unreviewed.

Proof route: `thompson-f-binomials-meet-ideals-with-separated-conjugates-proof`.
