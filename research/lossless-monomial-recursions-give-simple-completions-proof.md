---
rg: 2
id: lossless-monomial-recursions-give-simple-completions-proof
kind: route
title: Losslessness composes along branches, so no cancellation occurs; erasure plus a peel state gives scalar descendants
target: lossless-monomial-recursions-give-simple-completions
requires:
  - scalar-descendants-make-completions-simple
  - noninjective-ln-completions-have-self-similar-bases
---

Lane proof (bh-algebra, 2026-09-18). Notation as in the claim. Iterates are indexed so that
`ψ_N(a)_(ur, u'r') = ψ(ψ_(N−1)(a)_(uu'))_(rr')`.

1. **Branches.** For `μ = (i_1..i_N)`, induction on `N` gives that the only nonzero entry of `ψ_N(w)_(μ,·)`
   is `τ_(i_N)(… τ_(i_1)(w) …)`, in column `(δ_(i_1)(w), δ_(i_2)(τ_(i_1)(w)), …)`.
   - At each step the map `(ν, v) ↦ (ν δ_i(v), τ_i(v))` is injective, by (L).
   - So for fixed `μ`, `w ↦ (δ_μ(w), τ_μ(w))` is injective on words with nonzero image.
2. **No cancellation (part 1).** Let `b = Σ c_w w`. The `(μ, ν)` entry of `ψ_N(b)` is
   `Σ_(δ_μ(w) = ν) c_w τ_μ(w)`, a combination of pairwise distinct words by step 1. It vanishes exactly
   when every such `c_w` is `0`. So `ψ_N(b) = 0` iff `ψ_N(w) = 0` for every `w` with `c_w ≠ 0`.
   - Dying is upward closed in `N`, since `ψ_(N+1)` is `ψ` applied entrywise to `ψ_N`.
   - So `b ∈ J` iff every word of `b` dies, and `J` is the span of the dying words.
3. **Scalar descendants (part 2).** Let `0 ≠ b̄ ∈ B/J`. Write `b = Σ c_w w` over non-dying words, with
   `c_(w_0) ≠ 0`.
   - By (E), `τ_μ(w_0) = 1` in column `ν` for some branch `μ`.
   - By step 1 every other word contributing at `(μ, ν)` has `τ_μ(w) ≠ 1`, so it is a nonempty word.
   - The `(μ, ν)` entry is therefore `c_(w_0) + e`, with `e` a combination of nonempty words.
   - By (P), its `(p, p)` entry under `ψ` is `c_(w_0) ∈ K^x`.
   So every nonzero element of `B/J` has a scalar descendant. By `scalar-descendants-make-completions-simple`,
   the completion of `B/J` along the injective `ψ̄` is simple. By `noninjective-ln-completions-have-self-similar-bases`,
   it is `O_ψ(B)`, which is finitely presented and contains `B/J`.
4. **Application (part 3).** `K<x_1..x_m> ∩ J` is spanned by the words in the `x_i` that die, which are
   exactly those with a factor in `W`. That is the defining ideal of `M`. So `M -> B/J ⊆ O_ψ(B)` is
   injective. ∎
