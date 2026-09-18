---
rg: 2
id: fold-transfer-theorem-proof
kind: route
title: Normalize the determining normal to -e_2, fold, read every translate of x (x) y through the Busemann cocycle; freeness and orbit closures transfer exactly, rigidity by the one-sided path-fold transfer and the fold lemma
target: fold-transfer-theorem-for-fibres-with-a-determining-half-plane
requires:
  - abht-path-folds-accept-exactly-expansive-rational-half-planes
  - path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
  - recognizable-morphisms-give-kakutani-equivalent-z2-groupoids
---

Notation as in the target. `T` is the Cayley tree of `F_n` for the free basis `S`, so edges are `u — us`
and left multiplication is by tree automorphisms. For a flow `y` with end `ξ`, `h_y` is the height,
normalized by `h_y(1) = 0`. Along every edge it changes by `±1`, increasing along the flow. The shift
convention is ABHT's, `σ^g(z)(h) = z(g^(−1) h)`, and on `Z^2` it is `(σ^p x)(q) = x(q + p)`.

## Step 1. Checks 1–4 on (D)

- **Check 1, (D) ⇒ determining.**
  - `⟨·, ν⟩` takes integer values, and every `f ∈ F` has `⟨f, ν⟩ <= −1`.
  - If `x, x'` agree on `{⟨z, ν⟩ < t}`, induction on the level `⟨z, ν⟩ = t, t + 1, …` shows `x(z) = x'(z)`
    everywhere.
- **Check 1, determining ⇒ (D).**
  - Restriction to `{⟨z, ν⟩ < 0}` is a continuous injection of the compact `X`, so `x(0)` is a
    continuous function of it. It therefore depends on a finite window `F`, and `G` is that function.
  - Shift invariance gives (D) at every `z`.
- **Check 1, invariance.** Conjugacy invariance is Theorem B of
  `triangle-permutive-existence-iff-hex-cone-determinism`. `GL_2(Z)` sends `ν` to `M^(−T) ν`.
- **Checks 2–3.**
  - For Wang tiles, the tile at `z` is fixed by its bottom colour, the top colour of `z − e_2`, and its
    left colour, the right colour of `z − e_1`. So `F = {−e_1, −e_2}` and `⟨f, (1,1)⟩ = −1`.
  - A row rule has `F ⊆ Z × {1}`, so `ν = −e_2`.
- **Check 4.** Let `x, x'` agree on `H = {⟨z, ν⟩ < t}`.
  - Recognizability is local: Step 1 of `recognizable-morphism-kakutani-equivalence-proof` gives a radius
    `ρ` such that `x|_(p + B_ρ)` decides whether `p` is a block origin, and if so the parent letter.
  - The block origins of a point form a coset `p_0 + N Z^2`, since all images are `N × N`. One common
    origin deep in `H` gives `x` and `x'` the same coset.
  - Block letters agree at all `m` with `p_0 + Nm + B_ρ ⊆ H`. This contains a half-plane
    `{⟨m, ν⟩ < t'}`, because `Nν` is a positive multiple of `ν`.
  - So the parent points `y, y'` agree there, and (D) for `Y` gives `y = y'`. Then `x` and `x'` are the same
    translate of `ω(y)`, since their block cosets agree.

## Step 2. Normalization

- **The rule after `M`.** `GL_2(Z)` acts transitively on primitive vectors, so `M` exists. Then
  `MF ⊆ {f_2 >= 1}`, and the rule reads `x^M(z) = G(x^M|_(z + MF))`.
- **Vertical blocks.** The new letter at `(i, j − 1)` is `(x^M(i, j − 1), …, x^M(i, j + H − 2))`.
  - Its first entry is `G` of entries of the new letters of row `j` on `[i − R, i + R]`.
  - Its other entries lie in the new letter at `(i, j)`.
- **Nearest-neighbour form.** Widening the blocks horizontally and vertically past the forbidden-pattern
  radius makes the shift nearest-neighbour and keeps a one-row rule. This is the standard higher-block
  argument, as in Step 3 of `one-sided-path-fold-acceptance-proof`.

## Step 3. Item 1, structure

- **`Z = {x ⊗ y}`.** This is item 1 of `abht-path-folds-accept-exactly-expansive-rational-half-planes`,
  since `−e_2` is determining for `X̂`.
- **The map is a homeomorphism.** `(x, y) ↦ x ⊗ y` is continuous and onto. It is injective: `y` is the
  flow coordinate, and `x` is read off the rows along one flow line through `1`, where the heights take
  every integer value. The domain is compact.
- **Cocycle.** Let `g = w t^m` and `h = u t^i`. Then `gh = wu t^(i + m)`, since `t` is central.
  - `y_w(u) = y(wu)` is the flow `σ^(w^(−1)) y`.
  - Heights along edges are decided by the flow alone, so `h_y(wu) = h_y(w) + h_(y_w)(u)`.
  - Hence `(x ⊗ y)(gh) = (x(i + m, h_y(w) + h_(y_w)(u)), y_w(u))`, which is the stated formula.

## Step 4. Item 2, freeness

- **`X` free ⇒ `Z` free.** Suppose `g = w t^m ≠ 1` fixes `x ⊗ y`. By the cocycle and injectivity,
  `y_w = y` and `σ^((m, h_y(w))) x = x`.
  - If `w = 1`, then `m ≠ 0` and `x` has the period `(m, 0)`.
  - If `w ≠ 1`, then `y_w = y` means `w` fixes `ξ`, so `ξ` is an end of the axis of the hyperbolic `w`, and
    `h_y(w) = ±ℓ(w) ≠ 0`.
  - Either way `x` has a nonzero period.
- **`Z` free ⇒ `X` free.** Let `x` have a period `v ≠ 0`. Replacing `v` by `−v` if needed, `v_2 >= 0`.
  - If `v_2 = 0`, then `g = t^(v_1)` fixes every `x ⊗ y`.
  - If `v_2 > 0`, take `s ∈ S`, the end `ξ = s^∞` with its flow `y`, and `w = s^(v_2)`.
    - `w` fixes `ξ`, and the flow is `F_n`-equivariant, so `y_w = y`.
    - `w` lies on the ray from `1` to `ξ`, so `h_y(w) = v_2`.
    - So `g = w t^(v_1)` fixes `x ⊗ y`.
- **Transfer back.** `X̂` is free iff `X` is.

## Step 5. Item 3, minimality (`n >= 2`)

- **"⊆".** By the cocycle, every translate of `x ⊗ y` is `x' ⊗ y'` with `x'` a translate of `x`. The set
  on the right is closed, as the image of a compact set, and invariant.
- **"⊇".** Let `x* ∈ \overline{Z^2 · x}`, let `y*` be any flow, and let `B` be the ball of radius `r` at
  `1`.
  - **What is to be matched.** `(x* ⊗ y*)|_B` is determined by two things:
    - `y*|_B`, which is fixed by the first `r + 1` letters `u* = W*_0 … W*_r` of the ray from `1` to
      `ξ*` (the flow at a ray vertex at distance `r` is the next letter), and which also fixes the heights on `B`;
    - `x*` on the window `P = [−r, r]^2`.
  - **Matching `x*`.** Pick `p ∈ Z^2` with `σ^p x` equal to `x*` on `P`.
  - **Matching `y*`.** Pick a vertex `v` with `h_y(v) = p_2 + r + 1` and `y(v) ≠ (u*_r)^(−1)`.
    - Such `v` exist at every height, because the `2n − 1 >= 3` children of a vertex carry pairwise
      different flow letters.
    - Put `w = v (u*)^(−1)`. The path from `w` along `u*` reaches `v` and then continues up `v`'s ray
      without backtracking, so it is the flow ray from `w`.
    - Hence `y_w` agrees with `y*` on `B`, and `h_y(w) = p_2`.
  - **The translate.** Take `g = w t^(p_1)`. Then `σ^(g^(−1))(x ⊗ y) = (σ^p x) ⊗ y_w` agrees with
    `x* ⊗ y*` on `B`.
- **Conclusion.** So `Z` is minimal iff every orbit closure in `X̂` is all of `X̂`, iff `X` is minimal.

## Step 6. Items 4–6, rigidity and algebra

- **Item 4.** This is `path-fold-rigidity-transfer-proof`, applied to `X̂`, with (F1) given by item 1 and
  the radius-`R` downward rule `φ`. Its one-sided use is checked in `one-sided-path-fold-acceptance-proof`,
  Step 4.
- **Item 5.** This is `path-folded-sft-rigidity-pullback-proof`, with `β(w t^i) = (i, h_y(w))`: it is
  1-Lipschitz and onto, and `x ⊗ y ∈ Z` for every `x`. Rigidity passes between `X` and `X̂` because the
  crossed products are isomorphic (`sft-crossed-product-fp-iff-quantum-rigid`).
- **Item 6.** `F_n × Z` is finitely presented, so `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`
  applies. Items 2–3 and `free-minimal-cantor-crossed-products-are-central-simple` give central
  simplicity. The non-rigid clause is the contrapositive of `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
  ∎
