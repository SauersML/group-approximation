---
rg: 2
id: mosher-suffix-uniqueness-continuity-proof
kind: route
title: Iterate the suffix uniqueness step from the end of the word, whose choices depend only on the last n letters and a carry in the finite ball B_K
target: mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

Notation as in the target.

**Step 1 (the backward process).** Let `v ∈ 𝓛`, `a ∈ 𝒜`, and let `v' = v·a`. Then `v` and
`v'` are `K`-fellow travellers (automatic structure), with `g_0 = v̄^{-1} v̄' = a ∈ B_K`.
- By suffix uniqueness there is a unique suffix `s_0` of `v`, of length at most `n`,
  with `(s_0, g_0) ∈ 𝒮`. Moreover `v = ŵ_1 s_0` and `v' = ŵ'_1 F(s_0, g_0)`, where
  `ŵ_1, ŵ'_1` are `K`-fellow travellers.
- Both lie in `𝓛`, because `𝓛` is prefix closed. So `g_1 = ŵ̄_1^{-1} ŵ̄'_1`
  lies in `B_K`, and it equals `s̄_0 g_0 F(s_0,g_0)^{-1}`, the class of
  `s̄_0 · g_0 · (F(s_0,g_0))^{-1}`, since `v̄ = ŵ̄_1 s̄_0` and `v̄' = ŵ̄'_1 F̄`.
- Repeat with `(ŵ_1, ŵ'_1, g_1)`.
- Which suffix `s_i` is taken depends only on `g_i` and the last `n` letters of `ŵ_i`,
  because `𝒮` is finite and only suffixes of length at most `n` are tested.
- The output chunk `F(s_i, g_i)` and the next carry `g_{i+1}` depend only on
  `(s_i, g_i)`.
- The process consumes a nonempty suffix at each step, so it reaches the empty prefix.
  At that point `ŵ'` is a normal form fellow-travelling the empty word, hence the normal
  form of the element `g_J`, which is determined by `g_J`.
- So `v'` is the concatenation, from front to back, of: the normal form of `g_J`, then
  `F(s_{J-1}, g_{J-1})`, …, then `F(s_0, g_0)`. This is item 2.

**Step 2 (suffix-continuity).** Let `v, w ∈ 𝓛` have the same last `M = n(N+1)` letters.
Run the process on both with the same `g_0 = a`.
- Before step `t+1`, at most `tn` letters have been consumed. So at least `M − tn ≥ n`
  common letters remain, for every `t ≤ N`.
- So steps `1, …, N+1` see the same last `n` letters and the same carry. They choose the
  same `s_t`, emit the same chunks and produce the same carries.
- Each chunk `F(s,g)` is a suffix of length at least 1, so `v·a` and `w·a` share their
  last `N+1 ≥ N` letters. This is item 1.

**Step 3 (the inverted language).** Let `G` be a group and `𝒜` symmetric.
- **Normal forms.** `inv : 𝓛 → 𝓛^{inv}` is a bijection, and `π(inv(v)) = v̄^{-1}`. So
  `𝓛^{inv}` is a language of normal forms, and it is regular: reverse the automaton and
  rename letters by inversion.
- **Left action.** For `x ∈ 𝒜`, left multiplication by `x` on `𝓛^{inv}` sends `inv(v)`
  to `inv(v·x^{-1})`, since `x v̄^{-1} = (v̄ x^{-1})^{-1}`.
- **Prefixes and suffixes.** A common prefix of length `M` of `inv(v)` and `inv(w)` is a
  common suffix of length `M` of `v` and `w`.
- **Continuity.** By Step 2 applied to `a = x^{-1}`, the BBCMP Proposition 2.1 criterion
  holds with `S = 𝒜` and `M = n(N+1)`. So `𝓛^{inv}` is continuous.
- **Multiplier relations.** The left multiplier relation of `𝓛^{inv}` for `x` is
  `{(inv(v·x^{-1}), inv(v))}`. It is accepted deterministically by running Step 1 on
  the reversed input `inv(v)`, one chunk at a time, while reading off and checking the
  reversed output. The acceptor keeps a buffer of at most `n` letters and a carry in
  `B_K`, reads the input tape chunk by chunk, and compares each emitted chunk with the
  output tape. It is deterministic.
- **Synchronous case.** If `𝓛` is synchronous, its right multiplier relations have
  bounded length difference. Their reversals are then synchronous rational, since a
  bounded shift of the padding can be done with a finite buffer. □
