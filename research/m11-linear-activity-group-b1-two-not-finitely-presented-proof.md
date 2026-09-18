---
rg: 2
id: m11-linear-activity-group-b1-two-not-finitely-presented-proof
kind: route
title: Letter-by-letter sections never lengthen a word and move exponent mass by the matrix a -> a, c -> c + a; following a relation down sections with nonzero mass ends in stable words, where the odometer letters must alternate in sign while the root forces 11 | e_a, and the c-letters reduce to a relation in Z wr C_11; so e_a and e_c survive and the acyclicity bound kills finite presentation
target: m11-linear-activity-group-b1-two-not-finitely-presented
requires:
  - m11-linear-activity-self-replicating-group
  - fully-self-replicating-fp-infinity-groups-are-acyclic
  - tits-hosts-for-transitive-local-actions
artifacts:
  - experiments/m11-germ-characters-2026-09-18/exponent_descent.py
  - experiments/m11-germ-characters-2026-09-18/exponent_descent.out
---

The notation is that of the target. Maps act on the right, and words are read left to
right. The action is `(x w)^g = x^{π_g} w^{g|_x}`, so `(gh)|_x = g|_x h|_{x^{π_g}}`. For
`g ∈ Aut(X*)` and a vertex `u`, `g@u` acts as `g` below `u` and trivially elsewhere.

## 1. Letter sections

Let `S = M_11 ⊔ {a, b, c}`, and let `F = F(S)` with `R = F/N`. Letters in `M_11` are
**finitary**; the letters `a^{±1}, b^{±1}, c^{±1}` are **non-finitary**. For a letter `l`
and a point `y ∈ X`, the **letter section** `l|_y` is one letter or the empty word:

| letter | section at `1` | at `2` | at `3` | elsewhere | root |
|---|---|---|---|---|---|
| `a` | `a` | – | – | – | `α` |
| `a^{-1}` | – | `a^{-1}` | – | – | `α^{-1}` |
| `b^{±1}` | `b^{±1}` | `α^{±1}` | `β^{±1}` | – | `1` |
| `c^{±1}` | `c^{±1}` | `a^{±1}` | – | – | `1` |
| `p ∈ M_11` | – | – | – | – | `p` |

The row for `a^{-1}` uses `(g^{-1})|_y = (g|_{y^{π_g^{-1}}})^{-1}`; the other inverse rows
have trivial root, so their sections are just the inverted sections of the positive letter.

For a word `w = l_1 ⋯ l_L` and `x ∈ X`, put `y_1 = x` and `y_{i+1} = y_i^{π(l_i)}`. The
**raw section** is the concatenation `w|_x = l_1|_{y_1} ⋯ l_L|_{y_L}`, not reduced. It
represents the section of the element `w` at `x`.

**Lemma 1.** For every word `w`:

- (i) `|w|_x| ≤ nf(w) ≤ |w|`, where `nf(w)` counts non-finitary letters.
- (ii) `Σ_x e_c(w|_x) = e_c(w)`.
- (iii) `Σ_x e_a(w|_x) = e_a(w) + e_c(w)`.
- (iv) If `w ∈ N` then `w|_x ∈ N` for all `x`.
- (v) If `w` has no finitary letter, its root permutation is `α^{e_a(w)}`.

*Proof.*

- (i) Each non-finitary letter contributes at most one letter, and finitary letters
  contribute none.
- (ii), (iii) For fixed `i`, the map `x ↦ y_i` is a bijection of `X`, being a product of
  permutations. So each sum equals `Σ_i Σ_{y ∈ X} (exponent of l_i|_y)`. By the table,
  `c^{±1}` contributes `c^{±1}` once and `a^{±1}` once, and `a^{±1}` contributes `a^{±1}`
  once. No other letter contributes `a` or `c`.
- (iv) A trivial element has trivial sections.
- (v) Only `a^{±1}` has nontrivial root, and it is `α^{±1}`. ∎

## 2. Descent to stable cycles

A word over `{a, b, c}^{±1}` is **stable at `x`** if every letter `l_i` has a
non-finitary section `l_i|_{y_i}`. Equivalently, `|w|_x| = |w|` and `w|_x` has no finitary
letter. Stable cycles are defined as in item 4 of the target.

**Lemma 2 (descent).** Let `λ` be `e_a` or `e_c`, and suppose `Σ_x λ(w|_x) = λ(w)` for all
`w ∈ N`. If `λ` vanishes on every relation lying on a stable cycle, then `λ(N) = 0`.

The same proof works for any `R = ⟨P, Q⟩` whose letter sections lie in `Q^{±1} ∪ P ∪ {∅}`,
which is item 4 of the target.

*Proof.* Let `w_0 ∈ N` with `λ(w_0) ≠ 0`. Given `w_i ∈ N` with `λ(w_i) ≠ 0`, we have
`Σ_x λ(w_i|_x) = λ(w_i) ≠ 0`. So some `x_i` has `λ(w_i|_{x_i}) ≠ 0`. Put
`w_{i+1} = w_i|_{x_i}`, which lies in `N` by Lemma 1(iv).

By Lemma 1(i) the lengths do not increase. They are never `0`, since `λ ≠ 0` on every
`w_i`. So they are constant, equal to some `ℓ ≥ 1`, for `i ≥ i_0`.

For `i ≥ i_0` we get `ℓ = |w_{i+1}| ≤ nf(w_i) ≤ ℓ`. So `w_i` has no finitary letter, and
every letter of `w_i` contributes a letter. That letter is non-finitary, because
`w_{i+1}` has no finitary letter either. So `w_i` is stable at `x_i`.

There are finitely many words of length `ℓ` over `{a, b, c}^{±1}`, so the sequence
`(w_i)_{i ≥ i_0}` repeats. The part between two repeats is a stable cycle of relations,
all with `λ ≠ 0`. This contradicts the hypothesis. ∎

## 3. The group `⟨α, a⟩`

**Lemma 3.** `⟨α, a⟩ = N_a ⋊ ⟨α⟩`, where
`N_a = ⟨a@1, …, a@11⟩ ≅ ℤ^{11}` and `⟨α⟩ ≅ C_{11}`. The exponent sum of `a` descends to a
homomorphism `θ : ⟨α, a⟩ → ℤ`, with `θ(a) = 1` and `θ(α) = 0`.

*Proof.* `a α^{-1} = a@1`, and `α^{-(y-1)} (a@1) α^{y-1} = a@y`. The `a@y` have disjoint
supports and infinite order, since `a` does. So they generate a free abelian group of
rank `11`, and `α` permutes these generators. `N_a` acts trivially on `X` and `α` does not.
So `⟨α, a⟩ = N_a ⋊ ⟨α⟩`.

Let `θ` be the sum of the `N_a`-coordinates on `N_a`, extended by `θ(α) = 0`. It is a
homomorphism, because permuting coordinates preserves their sum. Also
`θ(a) = θ((a@1) α) = 1`. A word in `α^{±1}, a^{±1}` therefore has `θ` equal to its
`a`-exponent sum, and this is `0` when the word is trivial. ∎

## 4. `e_c` descends

**Proposition 4.** `e_c(N) = 0`.

*Proof.* Lemma 1(ii) gives the hypothesis of Lemma 2 for `λ = e_c`. Let
`w_0, …, w_p = w_0` be a stable cycle of relations, with `w_{i+1} = w_i|_{x_i}`. We show
`e_c(w_0) = 0`.

**Step 1: every `c`-letter is read at point `1`.** A letter `c^{±1}` read at point `1`
gives `c^{±1}`. Read at point `2` it gives `a^{±1}`. No other letter gives a `c`-letter.
So the number of `c`-letters does not increase along the cycle. It returns to its
starting value, so it is constant, and in every `w_i` every `c`-letter is read at point `1`.

**Step 2: where the letters sit.** Stability forces the following:

- every `b^{±1}` is read at point `1`;
- every `a` is read at point `1`, and moves the point to `2`;
- every `a^{-1}` is read at point `2`, and moves the point to `1`.

So in `w = w_0`, read from `x_0`:

- after an `a` the point is `2`. The next letter must be `a^{-1}`, since `b`, `c` and `a`
  all need point `1`;
- after an `a^{-1}` the point is `1`;
- if `x_0 = 2`, the first letter is `a^{-1}`;
- if `x_0 ∉ {1, 2}`, no letter can be read, which contradicts `ℓ ≥ 1`.

Hence `w` is freely equal to a word `U` over `{b, c}^{±1}`, or to `a^{-1} U a`, or to
`a^{-1} U`, or to `U a`. Every `a` is immediately followed by `a^{-1}`, except possibly a
final `a`. The root permutation of `w` is trivial, so the root forces `e_a(w) = 0`. Hence
`w` is `U` or `a^{-1} U a`, and `U = 1` in `R`, with `e_c(U) = e_c(w)`.

**Step 3: `U` passes to `⟨α, a⟩`.** The letters `b` and `c` have trivial root. So
`U|_2` is `U` with `b ↦ α` and `c ↦ a`, and it is a trivial word over
`{α, a}^{±1}`. By Lemma 3, `0 = θ(U|_2) = e_c(U) = e_c(w)`. ∎

## 5. `e_a` descends

**Proposition 5.** `e_a(N) = 0`.

*Proof.* By Lemma 1(iii) and Proposition 4, every `w ∈ N` satisfies
`Σ_x e_a(w|_x) = e_a(w)`. So Lemma 2 applies with `λ = e_a`.

Let `w` be a relation on a stable cycle, stable at `x`. It has no finitary letter, so by
Lemma 1(v) its root is `α^{e_a(w)} = 1`. Hence `11 | e_a(w)`.

By stability, as in Step 2 above:

- every `a` is read at point `1` and leaves the point at `2`;
- every `a^{-1}` is read at point `2` and leaves the point at `1`;
- the letters `b^{±1}` and `c^{±1}` do not move the point.

So consecutive `a`-letters alternate in sign, and `|e_a(w)| ≤ 1`. With `11 | e_a(w)` this
gives `e_a(w) = 0`. ∎

## 6. The theorem

*Item 1.* By Propositions 4 and 5, `(e_a, e_c)` induces a homomorphism `R → ℤ²` onto `ℤ²`.
Since `M_11` is perfect, `H_1(R)` is generated by `[a]`, `[b]` and `[c]`. The images of
`[a]` and `[c]` form a basis of `ℤ²`, and `[b]` lies in the kernel. So
`H_1(R) = ℤ[a] ⊕ ℤ[c] ⊕ ⟨[b]⟩`, and `b^{55} = 1`. Also `H_1(R; k) = H_1(R) ⊗ k` has
dimension at least `2`.

*Item 2.* `R ≅ R ≀_X M_11` by the target node. Here `|X| = 11`, and `M_11` is simple, so
`M_11 ≤ Alt(11)`, and `char ℚ = 0` does not divide `|M_11|`. By items 1 and 2(i) of
`fully-self-replicating-fp-infinity-groups-are-acyclic`, the two degree-1 basis classes
give `E_2 ≠ 0`. Then `h_2 = h_2 + dim E_2`, so `H_2(R; ℚ)` is infinite-dimensional. Type
`FP_2` over `ℚ` would make it finite-dimensional. Item 3(d) of that node says the same
directly.

*Item 3.* By item 4 of `m11-linear-activity-self-replicating-group`, which is item 4 of
`tits-hosts-for-transitive-local-actions`, `Γ⁺_R` is finitely presented iff `R` is.

*Item 4.* This is Lemma 2. ∎
