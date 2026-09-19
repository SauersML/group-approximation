---
rg: 2
id: m11-balanced-loop-host-is-not-finitely-presented-proof
kind: route
title: Proof that R° = <M_11, b, C> is not finitely presented, by the stable-relator lemma, the pure-power descent of weight-preserving section cycles, and theta-invariance of the section of sigma^k(alpha) at 1^k
target: m11-balanced-loop-host-is-not-finitely-presented
requires:
  - m11-balanced-loop-host-has-finite-h1
  - m11-balanced-loop-host-has-exact-finite-l-presentation
  - tits-hosts-for-transitive-local-actions
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - experiments/m11-balanced-loop-host-not-fp-2026-09-18/nonfp_checks.py
  - experiments/m11-balanced-loop-host-not-fp-2026-09-18/nonfp_checks.out
---

**Status: ESTABLISHED (unreviewed).** The proof is by hand, in the notation of the target.
The script (points coded `0..10`) supplies three finite facts:
- the words `W_α, W_β, W_b` are C-free and equal `α@1, β@1, b@1` exactly in `R°` (checked by
  the exact word-problem code of the sibling L-presentation);
- their free sections are `W_α|_1 = ω_α`, `W_β|_1 = ω_β`, `W_b|_1 = b`, and `W_α|_x`,
  `W_β|_x` are empty for `x ≠ 1`;
- `χ(ω_α)` is cyclically reduced with 14 syllables in `A = Z/55 * Z/55`.

The script also checks `σ^k(α)|_{1^k} = ω_α` for `k = 1, 2, 3` (lengths up to 4.7 million)
and runs the certificate of item 6.

## 0. The section homomorphism on free words

Letter sections define a homomorphism `Ψ : F → F ≀_X Sym(X)`. On letters it is given by
`α, β ↦` their root permutations, and by
`b|_1 = b, b|_2 = α, b|_3 = β, C|_4 = C, C|_5 = bα, C|_6 = C^{-1}`, with all other letter
sections trivial. The section `w|_x` of a free word is the `x`-coordinate of `Ψ(w)`, freely
reduced; iterating gives `w|_v` for vertices `v`. The map `F → R°` intertwines `Ψ` with the
wreath recursion of `R°`. So:
- `w|_v` represents `ḡ|_v`, where `ḡ` is the image of `w`;
- the level-`k` permutation of `w` is that of `ḡ`.

If `w ∈ K`, then `ḡ = 1`. So `w` acts trivially on every level and every `w|_v ∈ K`.

**Weight.** Let `wt` count letters `b^{±1}, C^{±1}`. A letter of weight 1 has sections of
weight at most 1, and `α, β` have empty sections. So `wt(w|_x) ≤ wt(w)`. Equality holds iff
two things are true. First, every state letter of `w` is read at a point where its section
has weight 1: `b^{±1}` at 1, and `C^{±1}` at 4, 5 or 6. Second, no state letters cancel in
the free reduction. Let `n_C` count letters `C^{±1}`. Then `n_C(w|_x) ≤ n_C(w)`, and a
`C`-letter read at 5 lowers `n_C`.

A section of `w` has length at most `2 wt(w)`. So the section closure of a finite set of
words is finite.

## 1. The stable-relator lemma (item 1)

Let `Q` be the section closure of `R`, and `Q^(k) = {q|_v : q ∈ Q, |v| = k} ∖ {1}`. Since
`Q^(1) ⊆ Q`, induction gives `Q^(k+1) ⊆ Q^(k)`. The sets are finite, so the chain stabilizes
at `Q^∞ = Q^(k_0)`, and `Q^∞ = Q^∞(1) := {q|_x : q ∈ Q^∞} ∖ {1}`.

Let `w = ∏_i f_i^{-1} r_i^{ε_i} f_i` with `r_i ∈ R`. Fix a vertex `v` with `|v| = k ≥ k_0`,
and work in `F ≀ Aut(X^k)` via the `k`-fold iterate `Ψ_k` of `Ψ`. Each `r_i ∈ K` has trivial
level-`k` permutation, so `Ψ_k(r_i) = (r_i|_u)_{|u| = k}`. Conjugation by
`Ψ_k(f_i) = (f_i|_u)_u π` gives coordinates `(f_i|_{u'})^{-1} r_i|_{u'} f_i|_{u'}`, where `u'`
is the vertex that `π` maps to the coordinate. Taking products, `w|_v` is a product of
`F`-conjugates of words `r_i|_u^{±1}` with `|u| = k`. These lie in `Q^(k) = Q^∞`, and
free reduction does not change the element of `F`. So `w|_v ∈ ⟨⟨Q^∞⟩⟩_F`.

## 2. Stable relators of `R°` are pure powers (item 2)

Let `Q ⊆ K` be finite and section-closed. Every `q ∈ Q^∞` is a section of an element of
`Q^∞`. Going backwards gives an infinite chain in a finite set. So `q` is an iterated section
of an element `p` that lies on a *section cycle* `p = p_0, p_1, …, p_n = p_0`, with `p_{i+1}`
a nonempty section of `p_i`.

- Weight 0 words have empty sections, so `wt(p_i) ≥ 1`. Along the cycle, `wt` and `n_C` are
  nonincreasing and return to their values, so they are constant.
- By §0, every state letter of `p_i` is read at a weight-1 point, and no `C`-letter is read
  at 5. The section is then the sequence of the images `b^{±1} ↦ b^{±1}` (read at 1) and
  `C^{±1} ↦ C^{±1}` or `C^{∓1}` (read at 4 or 6), and nothing cancels. So `p_{i+1}` contains
  no letters `α^{±1}, β^{±1}`. Since `p_0 = p_n`, every `p_i` is a word in `b^{±1}, C^{±1}`.
- A word without permutation letters is read at a single point `x`. If it contains `b`, then
  `x = 1`, and any `C`-letter would be read at 1 and lose weight. If it contains `C`, then
  `x ∈ {4, 6}` and it contains no `b`. So the reduced word `p_i` is `b^j` or `C^j`, `j ≠ 0`.
- `p_i ∈ K`. Now `C` has infinite order (`m11-balanced-loop-host-has-finite-h1`, item 1), so
  `C^j ∉ K`. And `b^j = (b^j, α^j, β^j, 1, …)` is trivial iff `55 | j`: `b^{55} = (b^{55},
  1, …)` is trivial, and for `55 ∤ j` one of `α^j, β^j` is not. So `p = b^{55j}`.
- The nonempty iterated sections of `b^{55j}` are `b^{55j}` (at 1), `α^{55j}` (at 2) and
  `β^{55j}` (at 3). Those of `α^{55j}` and `β^{55j}` are empty.

So `Q^∞ ⊆ {b^{55j}, α^{55j}, β^{55j}}`. For `Q_0`, part 5 of the script computes the chain
`48 → 21 → 9 → 3` words (after `R1`, whose sections are empty), ending at
`{b^55, α^55, β^55}`.

## 3. The section of `σ^k(α)` at `1^k` (item 3)

Let `θ` be the endomorphism of the free group `F_3 = F(α, β, b)` with `θ(α) = ω_α`,
`θ(β) = ω_β`, `θ(b) = b`. Since `W_s = s@1`, the root permutation of `ω_s` is that of `s`
for `s = α, β`, and `ω_α, ω_β` have empty sections.

- **(a) `σ(u)|_1 = θ(u)` for `u ∈ F_3`.** Each `W_s` has trivial root permutation, so
  `Ψ(σ(u)) = ∏ Ψ(W_{s_i})` has coordinate at 1 equal to `∏ W_{s_i}|_1 = θ(u)`.
- **(b) `θ(u)|_x = u|_x` for `u ∈ F_3`.** `Ψ ∘ θ = Ψ` on the generators: `ω_α, ω_β` have
  the root permutations of `α, β` and empty sections, and `θ(b) = b`. So `Ψ ∘ θ = Ψ` on
  `F_3`.

`σ` maps `F_3` to `F_3` because `W_α, W_β, W_b` are C-free. For `k ≥ 2`, (a) and then (b)
give `σ^k(α)|_{1^k} = θ(σ^{k-1}(α))|_{1^{k-1}} = σ^{k-1}(α)|_{1^{k-1}}`. By induction this
equals `σ(α)|_1 = ω_α`.

In `R°`, `σ^k(α)` represents `α@1^k` (apply `ι_1` `k` times), which has order 11 and acts
trivially on level `k`. So `w_k = σ^k(α)^{11} ∈ K`. Since `σ^k(α)` has trivial level-`k`
permutation, `w_k|_{1^k} = (σ^k(α)|_{1^k})^{11} = ω_α^{11}` in `F`.

## 4. Conclusion (items 4 and 5)

Suppose `R°` is finitely presented. By `fp-quotient-iff-kernel-finitely-normally-generated`,
`K = ⟨⟨R⟩⟩` for a finite `R`. Let `k_0` and `Q^∞` be as in §1. By §2,
`χ(Q^∞) = 1`, since `χ(b) = 1` and `α^{55}, β^{55}` map to 1 in `A`. For `k ≥ k_0`, §1 gives
`w_k|_{1^k} ∈ ⟨⟨Q^∞⟩⟩_F`, so `χ(ω_α)^{11} = χ(w_k|_{1^k}) = 1`. But `χ(ω_α)` is a cyclically
reduced element of syllable length 14 in the free product `A`, so it has infinite order.
This is a contradiction. So `R°` is not finitely presented.

`R°` is fully self-replicating with root image `M_11`
(`m11-balanced-loop-host-has-finite-h1`). By `tits-hosts-for-transitive-local-actions` its
Tits host `Γ⁺` is finitely presented iff `R°` is. So `Γ⁺` is not finitely presented.

## 5. The level-3 certificate (item 6)

`φ_3(w) = (χ(w|_v))_{|v|=3} · π_3(w)` is a homomorphism `F → A ≀ Aut(X^3)`. For `q ∈ Q_0`,
`π_3(q) = 1` and `q|_v ∈ Q^(3) = {b^55, α^55, β^55} ∪ {1}`, so `φ_3(q) = 1` and
`φ_3(⟨⟨Q_0⟩⟩) = 1`.

For `q = R2(C)`, `σ(q)` has trivial root, and its section at 1 is `∏ W_{c_i}|_{x_i}`, a word
of length 2 374 920. Below 1 the script finds six level-3 sections with nontrivial
`χ`-image, at `(1,4,5), (1,4,6), (1,4,7), (1,6,5), (1,6,6), (1,6,7)`. The first is `α^{-1}ω_α`.
Each has image of order 3 in `S_5` under `α ↦ (12345)`, `β ↦ (12453)`. So `φ_3(σ(q)) ≠ 1`,
already in the finite group `S_5 ≀ Aut(X^3)`. Hence `σ(Q_0) ⊄ ⟨⟨Q_0⟩⟩`.

By Theorems B and C of the sibling node, `θ : G_0 → G_0 ≀ M_11` is not injective, and
`K_0 ⊊ K_1 ⊊ ⋯`. This is a second proof of item 4 that relies on those theorems. The proof
in §4 does not.
