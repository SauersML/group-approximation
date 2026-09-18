---
rg: 2
id: thompson-f-z-wr-z-cosets-have-a-canonical-form-proof
kind: route
title: Tiles are permuted by a shift, a tile map commuting with the standard bump is a power of it, and slopes at the left ends fix the powers
target: thompson-f-z-wr-z-cosets-have-a-canonical-form
requires: []
---

Notation is as in the claim. Every element of `F` is an increasing PL homeomorphism of `[0,1]` with finitely many
dyadic breakpoints and slopes in `2^Z`, and it is linear near `0` and near `1`.

**Step 0 (facts about the tiles).**
- `x_0` is affine on each `I_k`, with image `I_{k+1}`. For `k ≥ 1` it is `t/2`, for `k = 0` it is `t − 1/4`, and for
  `k = −m ≤ −1` it is `2t − 1`, which sends `I_{−m}` to `I_{−m+1}`.
- So `x_0^k` maps `I_0` affinely onto `I_k`, and `h_k = x_0^k b_{I_0} x_0^{−k} = b_{I_k}`, since an affine conjugate
  of a standard bump is the standard bump of the image interval.
- The tiles have disjoint interiors, cover `(0,1)`, and are ordered like `Z`: `I_{k+1}` lies immediately to the left
  of `I_k`.
- `b_I(t) < t` on the interior of `I`, because `x_0(t) < t` on `(0,1)`. Its right slope at the left end of `I` is 1/2.
- **H is amenable.** The `h_k` have disjoint supports, so they commute. `x_0` conjugates `h_k` to `h_{k+1}`, so
  `A = ⟨h_k : k ∈ Z⟩` is an abelian normal subgroup of `H` with `H/A` cyclic. So `H` is metabelian, hence amenable.

**Step 1 (centralizer lemma).** Let `I = [a, b]` be a tile and `φ` an increasing PL homeomorphism of `I` with slopes
in `2^Z` that commutes with `b_I`.
- Let `2^m` be the right slope of `φ` at `a`. Put `ψ = φ b_I^m`. Its right slope at `a` is `2^m · 2^{−m} = 1`, and
  it still commutes with `b_I`. Since `ψ` is PL with slope 1 at `a` and fixes `a`, it is the identity on
  `[a, a + ε]` for some `ε > 0`.
- For `t ∈ (a, b)`, `b_I^j(t) ↓ a` as `j → ∞`: the sequence decreases and its limit is a fixed point of `b_I`.
  Choose `j` with `b_I^j(t) < a + ε`. Then `ψ(t) = b_I^{−j} ψ b_I^j (t) = t`.
- So `ψ = id` and `φ = b_I^{−m}` on `I`.

**Step 2 (`Stab_F(ξ) = H`).**
- *`H` fixes `ξ`.* `x_0·(I_k, h_k) = (I_{k+1}, h_{k+1})`. For `h = h_0`: it maps each tile onto itself, since its
  support is `I_0`, which it maps onto itself. It commutes with every `h_k`.
- *Conversely.* Let `f·ξ = ξ`. Then `f` permutes the tiles. Being increasing, it preserves their order, so it acts on
  the index set `Z` by an order automorphism, that is, by a shift: `f I_k = I_{k+s}` for all `k`. Matching the
  decorations gives `f h_k f^{−1} = h_{k+s}`.
- Put `d = x_0^{−s} f`. Then `d I_k = I_k` and `d h_k d^{−1} = x_0^{−s} h_{k+s} x_0^{s} = h_k`. By Step 1,
  `d|_{I_k} = h_k^{n_k}|_{I_k}` for integers `n_k`.
- `d ∈ F` is linear near 0 and fixes the points `2^{−j}` for all large `j`, so `d = id` near 0. Likewise near 1. Hence
  `n_k = 0` for all but finitely many `k`.
- The product `∏_k h_k^{n_k}` is then a finite product in `H`. It agrees with `d` on every tile, and the tiles cover
  `(0,1)`. So `d ∈ H` and `f = x_0^s d ∈ H`.

**Step 3 (bijection).**
- *Well defined.* For `η ∈ H`, `(ηg)^{−1}·ξ = g^{−1}·(η^{−1}·ξ) = g^{−1}·ξ`.
- *Injective.* If `g^{−1}·ξ = g′^{−1}·ξ`, then `g′ g^{−1} ∈ Stab(ξ) = H` by Step 2, so `Hg = Hg′`.
- *Equivariant.* `(gs)^{−1}·ξ = s^{−1}·(g^{−1}·ξ)`.

**Step 4 (normal form).** Fix `f` and write the elements of `fH` as `f x_0^s d` with `s ∈ Z` and `d = ∏ h_k^{n_k}`, a
finite product. This decomposition is unique because `H = A ⋊ ⟨x_0⟩`.
- *(N1) fixes `s`.* `f x_0^s d (I_0) = f(I_s)`, and the tiles `f(I_k)` of `f·ξ` are pairwise distinct. So (N1) holds
  iff `f(I_s)` is the tile of `f·ξ` containing `1/2` in `[p, q)`, that is, iff `f^{−1}(1/2) ∈ [a_s, b_s)`. That
  determines `s = k*`.
- *(N2) fixes the `n_k`.* Put `f′ = f x_0^{k*}`. On `I_k`, `f′ d` has image `f′(I_k)`, which does not depend on
  `d`. Its right slope at `a_k` is `σ_k 2^{−n_k}`, where `σ_k` is that slope for `f′`, because `h_k^{n}` has right
  slope `2^{−n}` at `a_k`. So (N2) holds iff `n_k = log_2 σ_k − ⌊log_2(|f′ I_k| / |I_k|)⌋`.
- *Finiteness.* If `f′` is affine on `I_k`, its slope there is `|f′ I_k|/|I_k| = σ_k`, a power of 2, so `n_k = 0`.
  `f′` has finitely many breakpoints, so it is affine on all but finitely many tiles. The required `d` is therefore a
  finite product and lies in `H`.
- So `fH` contains exactly one element satisfying (N1) and (N2). ∎

**Implementation remark.** `cosets.canon` computes `k*` from `f^{−1}(1/2)`. It then collects the tiles containing an
interior breakpoint of `f′`, builds `d` as a single PL map from rescaled copies of `x_0^{n_k}`, and returns the
composition `f′ d`, which is exact over `2^{−160}`. Every division is checked to be exact.
