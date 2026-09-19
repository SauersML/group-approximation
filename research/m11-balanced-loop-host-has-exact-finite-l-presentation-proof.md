---
rg: 2
id: m11-balanced-loop-host-has-exact-finite-l-presentation-proof
kind: route
title: Proof of the exact finite L-presentation of R° by a letter-weight descent tree that ends in pure powers, and of the level shift G_n = G_(n-1) wr M_11 that makes finite presentation equivalent to sigma(Q_0) in <<Q_0>>
target: m11-balanced-loop-host-has-exact-finite-l-presentation
requires:
  - m11-balanced-loop-host-has-finite-h1
  - m11-balanced-loop-host-h1-is-z55
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/rgroup.py
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/l_presentation_checks.py
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/l_presentation_checks.out
---

**Status: ESTABLISHED (unreviewed).** The proof is by hand, and the notation is that of the
target. The script (points coded `0..10`) checks:
- the explicit words `W_s`, where `W_s = s@1` holds exactly in `R°`;
- that the 48 words of `Q_0 ∖ R1` are trivial;
- the descent trees of 22 sample relators.

`rgroup.py` decides the word problem of `R°` exactly: `w = 1` iff every iterated section of
`w` has trivial root. Iterated sections of `w` have weight at most `weight(w)`, so there are
finitely many of them.

## 0. Conventions and the section homomorphism

For `g ∈ R°`, write `g = (g|_1, …, g|_11) π_g`. Right actions give
`(gh)|_x = g|_x · h|_{x^{π_g}}` and `π_{gh} = π_g π_h`.

On `F` define `Ψ(s) = ((s|_x)_x ; π_s)` for `s ∈ S`, with:
- `π_α = α` and `π_β = β`, with trivial sections;
- `π_b = π_C = 1`;
- `b|_1 = b, b|_2 = α, b|_3 = β` and `C|_4 = C, C|_5 = bα, C|_6 = C^{-1}`, with all other
  letter sections trivial.

This extends to a homomorphism `Ψ : F → F ≀_X Sym(X)`, and we write `Ψ(w) = ((w|_x)_x ; π_w)`.
Evaluation `ev : F → R°` satisfies `ev(w|_x) = ev(w)|_x` and `π_{ev(w)} = π_w`, because the
two sides agree on letters and both are cocycles. Hence:

**(0.1)** `w ∈ K` ⟹ `π_w = 1` and `w|_x ∈ K` for every `x`.

Conversely, `π_w = 1` and all `w|_x ∈ K` imply `w ∈ K`, since the action is faithful.

The **weight** `wt(w)` is the number of letters `b^{±1}, C^{±1}` in the reduced word `w`, and
`nC(w)` is the number of letters `C^{±1}`. A letter `b^{±1}` read at point `p` contributes a
weight-1 section if `p = 1`, and a weight-0 section otherwise. A letter `C^{±1}` contributes
weight 1 if `p ∈ {4,5,6}`, and weight 0 otherwise. At `p = 5` that section is `(bα)^{±1}`,
which has no `C`. Perm letters contribute nothing. Hence:

**(0.2)** `wt(w|_x) ≤ wt(w)` and `nC(w|_x) ≤ nC(w)`.

The word `w|_x` has length at most `2·wt(w)`. So the section closure of a finite set is
finite, which makes `Q_0` finite. The script finds 48 words outside R1. Sections of R1 words
are empty.

**(0.3) `Q_0 ⊆ K`, and `σ(K) ⊆ K`.**
- R1 holds in `M_11 ≤ R°`, and R0 holds because `b` has order 55. This is in
  `m11-balanced-loop-host-h1-is-z55`, and `rgroup.py` checks it directly.
- R2 is the wreath recursion of `b` and `C`, since `ev(σ(w)) = ev(w)@1`. Both sides are
  homomorphisms `F → R°` (`ι_1` is an endomorphism of `R°` by self-replication,
  `m11-balanced-loop-host-has-finite-h1`), and they agree on letters.
- R3 holds because `u@1` and `v@2` have disjoint supports.
- R4 holds because `h` is rooted with `1^h = 1`, so `h^{-1}(u@1)h = u@1`.
- C2 holds by (0.1) applied to `W_s ↦ s@1`.
- Sections of words in `K` lie in `K`, by (0.1).
- `σ(K) ⊆ K` because `ev∘σ = ι_1∘ev`.

So `K_n ⊆ K` for every `n`.

## 1. Rewriting modulo `K_0`

**Lemma 1.1.** Modulo `K_0 = ⟨⟨Q_0⟩⟩`, the following hold.
- (a) For `g` a word in `α, β` and `u ∈ F`, `g^{-1} ι_x(u) g ≡ ι_{x^g}(u)`. In particular
  `ι_x(u)` does not depend on the choice of `τ_x`.
- (b) `[ι_x(u), ι_y(v)] ≡ 1` for all `x ≠ y` and all `u, v ∈ F`.

*Proof.* (a) Let `τ = τ_{x^g}`. Then `1^{τ_x g τ^{-1}} = 1`, so `τ_x g = h τ` with `h` in
`Stab(1)`, modulo R1. By R4, `h` commutes with each `σ(s)`, hence with `σ(u)`. So
`g^{-1} τ_x^{-1} σ(u) τ_x g ≡ τ^{-1} h^{-1} σ(u) h τ ≡ τ^{-1} σ(u) τ`.

(b) `M_11` is 2-transitive, so pick `g` with `1^g = x` and `2^g = y`. By (a),
`[ι_x(s), ι_y(t)] ≡ g^{-1} [ι_1(s), ι_2(t)] g`. By (a) again, `ι_1(s) ≡ σ(s)`, since
`τ_1 ∈ Stab(1)`. So this is a conjugate of R3. Letters generate, so (b) follows for all
`u, v`. ∎

**Lemma 1.2 (decomposition).** For every `w ∈ F`,
`w ≡ ι_1(w|_1) ι_2(w|_2) ⋯ ι_11(w|_11) · \bar π_w (mod K_0)`, where `\bar π_w` is a word in
`α, β` for `π_w`.

*Proof.* Write `D(w)` for the right side.
- For `s = α, β`, `D(s) = s`.
- For `s = b, C`, `D(s) ≡ s` is R2. Here `ι_x` is multiplicative because `σ` is an
  endomorphism of `F`.
- If `D(u) ≡ u` and `D(v) ≡ v`, move `\bar π_u` to the right through `∏_y ι_y(v|_y)` using
  1.1(a). This gives `∏_x ι_x(v|_{x^{π_u}}) · \bar π_u`. Merge coordinatewise using 1.1(b).
  The result is `∏_x ι_x(u|_x v|_{x^{π_u}}) · \bar π_u \bar π_v = D(uv)`, up to R1.
- Inverses are similar. ∎

**Corollary 1.3.** If `π_w = 1` and `w|_x ∈ K_m` for all `x`, then `w ∈ K_{m+1}`.
Indeed, `\bar π_w ∈ ⟨⟨R1⟩⟩`, and `ι_x(w|_x) = τ_x^{-1} σ(w|_x) τ_x`. Also
`σ(K_m) ⊆ ⟨⟨σ(Q_0) ∪ … ∪ σ^{m+1}(Q_0)⟩⟩ ⊆ K_{m+1}`.

## 2. Theorem A: exactness via the descent tree

A word counts as a **leaf** if its reduced form is either a word in `α, β` (weight 0) or a
power `b^{j}` with `55 | j`. Every leaf in `K` lies in `K_0`, for these reasons:
- `ev` is injective on `⟨α, β⟩` (rooted automorphisms act faithfully), so a weight-0 word in
  `K` is a consequence of R1;
- `b^{55j}` is a consequence of R0.

For `w ∈ K`, the **descent tree** `T(w)` has root `w`. A non-leaf node `u` has as children
the nonempty reduced words `u|_x`, for `x ∈ X`. All nodes lie in `K`, by (0.1).

**Lemma 2.1.** `T(w)` is finite.

*Proof.* Each node has at most 11 children. By König's lemma, if `T(w)` were infinite it
would have an infinite path `w = u_0, u_1, u_2, …` of non-leaves with `u_{i+1} = u_i|_{x_i}`.
By (0.2), `wt(u_i)` and `nC(u_i)` are non-increasing, so both are constant for `i ≥ m`. Call
the constant weight `k`. We have `k ≥ 1`, because weight-0 words are leaves.

Fix `i ≥ m`. Since `wt(u_{i+1}) = wt(u_i)`, the following hold.
- Every letter `b^{±1}` of `u_i` is read at point 1, and every letter `C^{±1}` at a point of
  `{4,5,6}`.
- No letter `b^{±1}` or `C^{±1}` cancels when the section is freely reduced.

Since `nC` is constant, no `C^{±1}` is read at point 5, because that section `(bα)^{±1}` has
no `C`. So the letters of `u_{i+1}` come only from `b` at 1 (giving `b`) and from `C` at 4 or
6 (giving `C^{±1}`). Hence `u_{i+1}` has **no perm letters**.

Now consider `u_{m+1}`. It has no perm letters, and `b, C` have trivial root, so all its
letters are read at the same point `x_{m+1}`. If `u_{m+1}` contained both a `b^{±1}` and a
`C^{±1}`, then no single point would preserve the weight, since `b` needs point 1 and `C`
needs `{4,5,6}`. That contradicts `wt(u_{m+2}) = k`. So `u_{m+1}` is a reduced word in `b`
alone or in `C` alone, that is, `b^j` or `C^j` with `|j| = k ≥ 1`.
- `C` has infinite order (`m11-balanced-loop-host-has-finite-h1`), so `C^j ∉ K`.
- `b` has order 55, so `b^j ∈ K` forces `55 | j`, which makes `u_{m+1}` a leaf.

Either case contradicts the choice of the path. ∎

**Lemma 2.2.** If `T(w)` has height `h`, then `w ∈ K_h`.

*Proof.* By induction on height. Leaves lie in `K_0`. For a non-leaf `u` of height `h'`, the
children have height `< h'` and lie in `K_{h'-1}` by induction, and `π_u = 1` by (0.1). So
`u ∈ K_{h'}` by Corollary 1.3. ∎

**Theorem A.** By (0.3) and Lemmas 2.1 and 2.2, `K = ⋃_n K_n`. So `⟨S | Q_0 | σ⟩` is a
finite L-presentation of `R°`. ∎

*Remark.* The only input beyond the recursion is `ord(b) = 55` and `ord(C) = ∞`. The same
argument works for any group of this "balanced" shape, where every non-rooted letter passes
its weight to its own letter at a fixed set of points, and passes it to a different
non-rooted letter only by decreasing a well-founded count (here `nC`).

## 3. Theorem B: the level shift

**Lemma 3.1.** For `u ∈ F`, `σ(u)|_1 ≡ u` and `σ(u)|_x ≡ 1` for `x ≠ 1`, modulo `K_0`.

*Proof.* Each `σ(s) = W_s` has `π_{W_s} = 1`. So `σ(u)|_x = ∏_i W_{s_i}|_x` for
`u = s_1 ⋯ s_r`, with inverses handled as usual. Now apply C2 in each factor, using that
`K_0` is normal. ∎

**Theorem B.** Fix `n ≥ 1`, and let `Φ_n : F → G_{n-1} ≀_X M_11` be `Ψ` followed by
reduction mod `K_{n-1}`. Then `Φ_n` is onto and `ker Φ_n = K_n`, so
`G_n ≅ G_{n-1} ≀_X M_11`.

*Proof.* `Φ_n` is a homomorphism because `Ψ` is.

- **`K_n ⊆ ker Φ_n`.** Take `q ∈ Q_0`. Then `π_q = 1` and `q|_x ∈ Q_0 ⊆ K_{n-1}`, since `Q_0`
  is section-closed. For `1 ≤ j ≤ n`, Lemma 3.1 gives `σ^j(q)|_1 ≡ σ^{j-1}(q)`, which lies in
  `K_{j-1} ⊆ K_{n-1}`, and `σ^j(q)|_x ∈ K_0` for `x ≠ 1`. Also `π_{σ^j(q)} = 1`.
- **`ker Φ_n ⊆ K_n`.** This is Corollary 1.3 with `m = n − 1`.
- **Onto.** By Lemma 3.1, `Φ_n(σ(s)) = ((s K_{n-1}, 1, …, 1) ; 1)`. Conjugating by `τ_x`
  moves it to coordinate `x`. These elements, together with `Φ_n(α)` and `Φ_n(β)`, generate
  `G_{n-1} ≀ M_11`. ∎

**Corollary B.1.** For `n ≥ 1`, `K_{n+1} = K_n ⟺ K_n = K_{n-1}`.

*Proof.*
- (⇐) Then `Φ_{n+1} = Φ_n` as maps out of `F`, so their kernels agree.
- (⇒) Let `u ∈ K_n`. Then `σ(u) ∈ K_{n+1} = K_n = ker Φ_n`, so `σ(u)|_1 ∈ K_{n-1}`. By
  Lemma 3.1, `u ≡ σ(u)|_1 mod K_0`, so `u ∈ K_{n-1}`. ∎

Iterating, the chain `K_0 ⊆ K_1 ⊆ ⋯` is either constant or strictly increasing at every
step.

## 4. Theorem C: the criterion

- If `σ(Q_0) ⊆ K_0`, then `K_1 = K_0`, so `K_n = K_0` for all `n` by B.1. Then `K = K_0` by
  Theorem A, and `R° = ⟨S | Q_0⟩` is finitely presented.
- Conversely, suppose `R°` is finitely presented. Then `K` is the normal closure of finitely
  many elements (`fp-quotient-iff-kernel-finitely-normally-generated`, with `F` free of
  finite rank). Each such element lies in some `K_n`, so `K = K_N` for some `N`. The chain
  therefore stabilizes, so it is constant, and `σ(Q_0) ⊆ K_1 = K_0`.
- Finally, `θ = Φ_1` induces a map on `G_0` because `K_0 ⊆ K_1 = ker Φ_1`, and
  `ker θ = K_1/K_0`. So `θ` is injective iff `K_1 = K_0`.

If `R°` is not finitely presented, the chain is strictly increasing, so each map
`G_n ↠ G_{n+1}` has nontrivial kernel. Each `G_n` is finitely presented, since `K_n` is the
normal closure of a finite set. Their direct limit is `F/⋃K_n = R°`. ∎

## 5. Theorem D: the ascending HNN extension

In `Γ = ⟨S, t | Q_0, t^{-1} s t = σ(s)⟩` we have `t^{-1} w t = σ(w)` for every `w ∈ F`. So
`σ^j(q) = t^{-j} q t^{j} = 1` for all `q ∈ Q_0` and `j ≥ 0`. By Theorem A, the relations of
`Γ` are equivalent to `K`, together with `t^{-1} s t = σ(s)`. So `Γ = ⟨R°, t | t^{-1} g t =
ι_1(g)⟩` is the ascending HNN extension along the injective endomorphism `ι_1`. The base
embeds, by Britton's lemma for ascending HNN extensions. `Γ` is finitely presented by
construction. ∎

## 6. What the script certifies (`l_presentation_checks.out`)

- The weight-preserving letter/point pairs are exactly those used in (0.2) and Lemma 2.1.
- `b^k = 1` for `k < 200` exactly when `55 | k`, and `C^k ≠ 1` for `0 < k ≤ 60`.
- Words `W_α, W_β, W_b, W_C` of weights 18, 20, 39, 10079 are built and checked exactly to
  equal `s@1`.
  - `W_α` and `W_β` come from the single-point commutators `[b, b^g]` (896 of them, at
    points 2 and 3), conjugated by `b^h`.
  - `W_C` comes from `[C, π_1] = C@6 · (C^{-1})@7` and `C = π^{-1}[C,π_1]π · (bα)@5`, where
    `π_1 = α³βα²β` and `π = α²βα²β`. The words are `aaaeaaea` and `aaeaae` in the script.
- `Q_0 ∖ R1` has 48 words, of maximum length 318 956 and 1 805 338 letters in total, and
  every one is trivial in `R°`.
- Descent trees were run on 22 sample relators: R0, R2, R3, R4, C2, `σ(R2)`, conjugates, and
  torsion relators `u^{ord(u)}` with `ord(u)` up to 275. All are finite, of height at most 1,
  with leaves as in §2.

The script does not test `σ(Q_0) ⊆ ⟨⟨Q_0⟩⟩`. That is the open step, and §7 describes it.

## 7. The remaining step

By Theorem C, FP_2 for `R°` is equivalent to `σ(Q_0) ⊆ ⟨⟨Q_0⟩⟩`. The rewriting of §1 reduces
this to the self-consistency of `ι_1` inside `G_0`: whether `⟨W_α, W_β⟩ ≤ G_0` satisfies R1,
and whether `W_b` and `W_C` satisfy R0 and R2 "one level down", modulo `K_0` only.

- **Positive route.** Derive `σ(r) ∈ K_0` for `r ∈ R1`. By §1, `W_α` and `W_β` are products
  of the elements `ι_2([α,β])^{ι_1(·)}`, so this is a statement about `ι_2(M_11)` in `G_0`.
  The other relators then follow by Lemma 1.2.
- **Negative route.** Find a quotient `H` of `G_0` in which some `σ(q) ≠ 1`, for example a
  permutation quotient of `G_0` that does not factor through `θ`.
