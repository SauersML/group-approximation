---
rg: 2
id: z2-o2-actions-anti-inner-and-o3-rokhlin-criterion-proof
kind: route
title: At p = 2 the transfer identities 1 + φ = 0 and 1 + ψ = 0 make φψ fix the unit class, Cuntz comparison produces the anti-invariant implementing unitary, and O_3 is the unit class of order two
target: z2-o2-actions-anti-inner-and-o3-rokhlin-criterion
requires:
  - o2-central-sequence-k-theory-bi-cyclotomic-transfer
  - o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
---

Notation is that of `o2-central-sequence-k-theory-bi-cyclotomic-transfer` and
its proof route: `C = A_∞ ∩ A'`, standard inputs (RS), (CU), (FC), and
Steps 0–5 there.

**Step A: a second proof of `N_φ = 0`, without crossed products.**  This is an
independent check of item 2 of the transfer node, for any finite abelian `G`.
- By item 1 of `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`
  (quasi-free `O_∞` absorption), there are isometries `s_g ∈ C` with orthogonal
  ranges and `α_h(s_g) = s_(hg)`.
- Define `ρ : C → F^α` by `ρ(c) = Σ_g α_g(s_1 c s_1*) = Σ_g s_g α_g(c) s_g*`.
  - It is a \*-homomorphism, because the ranges are orthogonal.
  - Its image is fixed.
  - Its image commutes with `A`, because `s_g, α_g(c) ∈ A'`.
- For `f ∈ F^α`, `ρ(f) = Σ_g s_g f s_g*`.  With `t_χ = |G|^(−1/2) Σ_g χ(g) s_g`,
  orthogonality of characters gives `Σ_g s_g f s_g* = Σ_χ t_χ f t_χ*`.
- Each `t_χ` is an eigen-isometry for `χ̄`, so `K_*(ρ ∘ i) = Σ_χ φ_χ = N_φ` by
  (FC).
- `ρ ∘ i` factors through `C`, and `K_*(C) = 0` (Step 0).  So `N_φ = 0`.

The same argument for `(B, α̂)` uses isometries `S_χ ∈ B_∞ ∩ B'` permuted by
`α̂`, and gives `N_ψ = 0` when `B ≅ O_2`.

**Step B: `φ = ψ = −1` at `p = 2`.**  For `G = Z/2`, `N_φ = 1 + φ` and
`N_ψ = 1 + ψ`.
- Item 2 of the transfer node (or Step A) gives `φ = −1` on `M_*` for every
  outer `α`.
- If the crossed product is KK-contractible, it also gives `ψ = −1`.
- So then `φψ = 1` on `M_*`.

**Step C: item 2(a).**  Apply item 3 of the transfer node at `(λ, h) = (χ, σ)`.
- `φ_χ ψ_σ [1] = [1]`, so there is a unitary `w ∈ A_∞` with `σ(w) = −w` and
  `w* a w = σ(a)` for all `a ∈ A`.
- Lift `w` to unitaries `w_n ∈ A`, using functional calculus on lifts that are
  close to unitaries.  They satisfy `‖σ(w_n) + w_n‖ → 0` and
  `w_n* a w_n → σ(a)`.
- *The unitary `W = w u`.*
  - From `w* a w = σ(a)` we get `a w = w σ(a)`, so `W a = w σ(a) u = a w u = a W`.
  - `u W u* = σ(w) u = −W`.
  - `α̂(W) = w(−u) = −W`.
- *Conversely,* let `W ∈ B_∞` be a unitary with `α̂(W) = −W`, `W ∈ A'` and
  `u W u* = −W`.
  - Write `W = x_0 + x_1 u`.  `α̂(W) = −W` forces `x_0 = 0`.
  - `W ∈ A'` gives `a x_1 = x_1 σ(a)`.
  - `u W u* = −W` gives `σ(x_1) = −x_1`.
  - So `w = x_1` is a unitary as above.

**Step D: `2[1] = 0` iff `O_3` embeds unitally into `F^α`.**
- If `O_3 ⊆ F^α` unitally, then `1 = Σ_(i=1)^3 s_i s_i*` gives `[1] = 3[1]`.
- Conversely, `F^α` contains a unital `O_∞`, with isometries `t_1, t_2, t_3` of
  orthogonal ranges.  Put `P = Σ t_i t_i*`.  Then `[P] = 3[1] = [1]`.
  - `P` is properly infinite, since it dominates `t_1 t_1* ~ 1`.
  - `P` is full, for the same reason.
  - By (CU) there is `c ∈ F^α` with `c*c = P` and `cc* = 1`.
  - `s_i = c t_i` satisfy `s_i* s_j = t_i* P t_j = δ_ij` and
    `Σ s_i s_i* = cPc* = 1`.

**Step E: item 1.**  Item 3 of the transfer node at `h = 1` says:
`α̂` is strongly approximately inner iff `A_∞ ∩ A'` contains an anti-invariant
unitary iff `φ[1] = [1]`.  With `φ = −1`, this is `−[1] = [1]`, that is
`2[1] = 0`.  Step D finishes.

**Step F: item 2(b).**  Assume `B ≃_KK 0`.
- `α` is strongly approximately inner iff `ψ[1] = [1]` (transfer node, item 3
  at `λ = 1`), iff `−[1] = [1]` (Step B), iff `2[1] = 0`.  With item 1, the
  second through fifth bullets of 2(b) are equivalent.  No Izumi is needed so
  far.
- *Strongly approximately inner ⟹ Rokhlin.*  Izumi I, Theorem 4.6, as cited in
  `izumi-rokhlin-approximately-representable-duality`, gives approximate
  representability.  Item 4 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`
  gives the Rokhlin property.
- *Rokhlin ⟹ `2[1] = 0`.*  Rokhlin gives `[1] = 0` (item 2 of
  `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`).
- *Rokhlin ⟺ `M_* = 0`.*  This is item 3 of the transfer node.

**Step G: item 3.**
- By item 3 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, detection
  at `2` is equivalent to Rokhlin rigidity for outer `Z/2`-actions on `O_2`
  with contractible crossed product.  Item 2(b) turns that into the `O_3`
  criterion.
- *The sign obstruction.*  Let `v` be an anti-invariant central unitary.
  - Then `wv` is an invariant unitary, and `(wv)* a (wv) = v* σ(a) v = σ(a)`.
  - Conversely, if `w'` is an invariant implementing unitary, then `w'* w`
    commutes with `A`, is anti-invariant and is unitary.
  - By item 1, such a `v` exists iff `2[1] = 0`.

**Step H: item 4.**  Let `Λ = Z[x, y]/(Φ_p(x), Φ_p(y))`, free over `Z` with
basis `x^i y^j`, `0 ≤ i, j ≤ p − 2`.
- By item 4 of the transfer node, `Λ[1/p] ≅ ∏_(j∈(Z/p)^×) Z[ζ_p, 1/p]`, with
  `y = x^j` on factor `j`.
- On factor `j`, the factor `1 − x^(−k) y` of the product is `1 − ζ_p^(j−k)`,
  which vanishes for `k = j`.  So the product vanishes in `Λ[1/p]`, hence in
  `Λ`, because `Λ` is torsion-free.
- For odd `p`, no single factor vanishes in `Λ`: factor `k` is nonzero on
  factor `j ≠ k`.  So `Λ` itself, with the element `1`, is a module in which
  no single twisted relation holds.
- For `p = 2`, `Λ = Z`, `x = y = −1`, and the single factor is `1 − xy = 0`.
