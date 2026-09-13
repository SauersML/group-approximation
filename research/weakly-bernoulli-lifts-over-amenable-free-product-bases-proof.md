---
rg: 2
id: weakly-bernoulli-lifts-over-amenable-free-product-bases-proof
kind: route
title: Quotient a free action of the extension over an amenable base, glue almost-lifts syllable by syllable over free products, and read non-splitting off the invisible center
target: weakly-bernoulli-lifts-over-amenable-free-product-bases
requires:
  - amenable-free-actions-weakly-equivalent-to-bernoulli
  - weakly-bernoulli-lift-iff-bernoulli-almost-lifts
  - abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
---

Notation as in the claim; `σ` is a set-theoretic section of `π` with `σ(1) = 1`.

## Item 1 (amenable bases)

Let `X` be a free p.m.p. `W`-action.
- **Well-defined action.** `Q` acts on `X/N` by `q·[x] = [w x]` for any `w ∈ π^-1(q)`. This is well defined because
  `w n x = (w n w^-1) w x` and `N` is normal. The quotient carries the pushforward measure. Since `N` is finite and
  acts freely, `X/N` is a standard non-atomic probability space and `Q` preserves the measure.
- **Freeness.** If `q·[x] = [x]`, then `w x = n x` for some `n ∈ N`, so `n^-1 w` fixes `x`. Off the null set of
  points fixed by some nontrivial element of `W`, this forces `w = n`, so `q = 1`.
- **Liftable.** The fibres of `X -> X/N` are single free `N`-orbits, so `X/N` is liftable by definition.
- **Weak equivalence.** `X/N` is weakly equivalent to `[0,1]^Q` by `amenable-free-actions-weakly-equivalent-to-bernoulli`.

## Item 2 (free products)

*The extension is an amalgam.* Put `W_i = π^-1(Q_i)`. `N` is normal in both `W_i`, so it is normal in
`W_1 *_N W_2`, with quotient `Q_1 * Q_2`. The natural map `W_1 *_N W_2 -> W` is onto, injective on `N`, and induces
the identity on quotients. So it is an isomorphism, and a cocycle on `Q × Y` lifting to `W` may be defined factor
by factor.

*Almost-lifts on the factors.* Let `B = [0,1]^Q`.
- If `Q_i` is infinite, `B|_(Q_i)` is a Bernoulli shift of `Q_i` with non-atomic standard base `[0,1]^(Q_i \ Q)`, so it
  is isomorphic to `[0,1]^(Q_i)`.
  - If `Q_i` is amenable, item 1 gives a liftable free action weakly equivalent to it. Then (1) ⇒ (2) of
    `weakly-bernoulli-lift-iff-bernoulli-almost-lifts`, for `Q_i` and `W_i`, gives almost-lifts on `B|_(Q_i)`.
  - Otherwise almost-lifts on `B|_(Q_i)` are the hypothesis.
- If `Q_i` is finite, `B|_(Q_i)` is free, so there is a Borel transversal `D` for its orbits. Writing `y = q d` with
  `d ∈ D`, `φ_i(q', q d) = σ(q' q) σ(q)^-1` is an exact lift: `φ_i(q_1, q_2 q d) φ_i(q_2, q d) = σ(q_1 q_2 q) σ(q)^-1`.

*Normalisation.* The defect set of the pair `(1, 1)` contains `{φ_i(1, ·) ≠ 1}`. Redefining `φ_i(1, ·) = 1`
therefore at most doubles the defect bound on the pairs in `F_i`.

*Gluing.* Fix a finite `F ⊂ Q` and `ε > 0`.
- Let `L` be the largest syllable length of an element of `F`, and `S_i ⊂ Q_i` the set of syllables from `Q_i`
  occurring in the normal forms of elements of `F`.
- Put `F_i = {1} ∪ S_i ∪ S_i^-1 ∪ S_i S_i`, and choose `φ_i` on `F_i × B`, normalised, with defect `< δ = ε/(L+1)` on
  pairs from `F_i`.
- For `q` with normal form `s_1 ⋯ s_m`, where `s_j ∈ Q_(i_j) \ {1}` alternate, define
  `φ(q, y) = φ_(i_1)(s_1, s_2 ⋯ s_m y) ⋯ φ_(i_m)(s_m, y)`, and `φ(1, y) = 1`. Then `π(φ(q, y)) = q`.

*Defect bound.* Take `q_1 = s_1 ⋯ s_m` and `q_2 = t_1 ⋯ t_l` with `q_1, q_2, q_1 q_2 ∈ F`.
- Reducing `s_1 ⋯ s_m t_1 ⋯ t_l` to normal form performs `k` cancellations `s_(m-j) t_(j+1) = 1` (`j < k`), then at
  most one merge `s_(m-k) t_(k+1) = u ≠ 1` in a common factor.
- In the product `φ(q_1, q_2 y) φ(q_2, y)` the factors meet in adjacent pairs `φ_i(s, t z) φ_i(t, z)` at points
  `z = t_(j+2) ⋯ t_l y`.
  - At a cancellation such a pair equals `φ_i(1, z) = 1` off the defect set of `(s, t)` at `z`.
  - At the merge it equals `φ_i(u, z)` off that defect set.
- All pairs involved lie in `F_i`, and each exceptional set is a measure-preserving translate of a set of measure
  `< δ`.
- Off their union, of measure `< (k+1) δ <= ε`, the product equals the defining product for the normal form of
  `q_1 q_2`, each remaining syllable being evaluated at the suffix of that normal form applied to `y`.

So condition (2) of `weakly-bernoulli-lift-iff-bernoulli-almost-lifts` holds for `Q`, and (2) ⇒ (1) there gives a
liftable free action weakly contained in `B`. That action is weakly equivalent to `B` by the addendum.

## Item 3 (instances)

*Invisibility.* By `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, every finite-dimensional unitary
representation of `Γ_p` kills `c_p ≠ 1`. A homomorphism onto a finite group `G`, composed with the regular
representation of `G`, is such a representation and is faithful on `G`. So `c_p` dies in every finite quotient.

*Properties of `Q_p = Γ_p / C`.*
- Infinite: `Γ_p` is infinite and `C` is finite.
- Finitely presented: `Γ_p` is, and `C` is finite.
- Amenable: a quotient of the solvable group `A_p`.
- `W = Γ_p` is not residually finite, by invisibility.

*Properties of `Q_p * Z`.*
- Non-amenable: it contains a free subgroup of rank two, since `|Q_p| >= 3`.
- No property (T): property (T) passes to quotients, and `Q_p * Z` maps onto `Z`.
- `W' = Γ_p *_C (C × Z)` is a central extension of it: `C` is central in both factors, hence in the amalgam.
- `W'` is not residually finite: `Γ_p` embeds in `W'`, and `c_p` dies in every finite quotient of `Γ_p`, hence of `W'`.

*No virtual splitting.* Suppose `π^-1(Q_0) = C × Q_0'` with `[Q : Q_0] < ∞`, `Q_0' ≤ W` and `Q_0' ∩ C = 1`. The kernel
`K` of the action of `W` on the finite set `W/Q_0'` lies in `Q_0'`, so `c_p ∉ K`. Then `c_p` survives in the finite
quotient `W/K`, a contradiction. The same argument applies to `W'`.

Items 1 and 2 apply to `Q_p` and to `Q_p * Z` (with `Q_2 = Z` amenable). ∎
