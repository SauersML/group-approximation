---
rg: 2
id: free-rewritable-tape-layers-kill-finite-presentation-proof
kind: route
title: Run the necessity theorem's orbit representation with matrix units in place of idempotents, then feed it a slot family from a proper colouring of the neighbourhood graph
target: free-rewritable-tape-layers-kill-finite-presentation
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity-proof
  - v-times-ample-full-groups-are-generated-by-transpositions
  - nekrashevych-symmetric-and-alternating-full-groups
  - ample-groupoid-products-expansive-iff-factors-are
---

Notation is that of the target. The architecture is that of
`fp-v-times-subshift-full-groups-force-quantum-rigidity-proof` (Sections 0–2), and only the changes are proved
in full. The rest is standard: Tietze; the facts that `M_N(k)` is simple and that every `M_N(k)`-module is a
direct sum of copies of `k^N`; Baire's theorem.

## 0. Normal forms with rewrites

**Lemma N′.** Every `g ∈ F(T')` has data `(u_i, v_i, F_i, π_i, π_i', λ_i)`, finitely many tuples, with:
- `u_i, v_i` finite binary words, `F_i ⊆ Λ` finite, `π_i ∈ (B × A)^(F_i)`, `π_i' ∈ A^(F_i)` and `λ_i ∈ Λ`;
- the rectangles `[u_i] × [π_i]` partition `C × X`;
- `g(u_i w, ξ) = (v_i w, λ_i . ρ_i(ξ))` on `[u_i] × [π_i]`, where `ρ_i` replaces the tape letters on `F_i`
  by `π_i'` and changes nothing else.

*Proof.* `g` is a compact open bisection with source and range `C × X`. A basis of `T'` consists of products
of `{[f, c] : c ∈ U}` (`f ∈ V`, `U` open) with `{(λ, ρ(ξ), ξ) : ξ ∈ W}`. Here `W` is a cylinder and `ρ` is a
fixed rewrite of the tape on a finite window inside the window of `W`. These sets form a basis of the
inductive-limit topology of `ℋ` and of `Λ ⋉ ℋ`. Cover `g` by finitely many of them, refine to a common
partition by cylinders, and use that `V` acts by prefix replacements on small cylinders. `∎`

**Constants.** `Γ` has a presentation on a finite set `Σ`, closed under inverses and containing every `t_s`
and `e_a`. Every relator has length `<= n`, and every generator has data with `F_i ⊆ B_r` and `|λ_i| <= ℓ`.
Put `R = nℓ + r`. `C_0 ⊆ C` is the dense set of eventually-zero sequences, preserved by prefix replacements.
- `t_s` has the single tuple `(∅, ∅, ∅, ∅, ∅, s)`.
- `e_a` has the tuples with window `{1}`, no rewrite (`π' = π_A`), `C`-parts `(00,01)`, `(01,1)`, `(1,00)`
  when the tape letter is `a`, and `(∅,∅)` otherwise, for every `B`-letter.

## 1. Tape families and the orbit representation

**Definition.** A *`D`-tape family* on a `k`-vector space `W_0` is a family of operators `E_(ab)(q)`,
for `a, b ∈ A` and `q ∈ Λ`, such that:
- (T1) for each `q`, `E_(ab)(q) E_(cd)(q) = δ_(bc) E_(ad)(q)` and `Σ_a E_(aa)(q) = I`;
- (T2) `E_(ab)(q)` commutes with `E_(cd)(q')` whenever `q ≠ q'` and `d(q, q') <= 2D`.

There is no analogue of the constraint axiom (Q3), since the tape is unconstrained.

**The representation.** Fix a point `y* ∈ Y` and put `W = k[C_0] ⊗ k[Λ] ⊗ W_0`. For `F ⊆ B_r`,
`π ∈ (B × A)^F`, `π' ∈ A^F` and `z ∈ Λ`, put

    N_(π,π')(z) = [y*(z^(-1) f) = π_B(f) for all f ∈ F] · ∏_(f ∈ F) E_(π'(f) π_A(f))(z^(-1) f).

The factors sit at distinct sites of a set of diameter `<= 2r`. For `D >= r` they commute by (T2), so the
order does not matter. For `σ ∈ Σ` with data as above, set

    ψ(σ)(δ_c ⊗ δ_z ⊗ u) = Σ_(i : c ∈ [u_i]) δ_(v_i w_i) ⊗ δ_(λ_i z) ⊗ N_(π_i,π_i')(z) u,   c = u_i w_i.

**A comparison point.** Choose `x* ∈ A^Λ` such that `g.x*` and `x*` differ at infinitely many sites for every
`g ≠ 1`.
- It exists by Baire. For `g ≠ 1` and finite `F`, the closed set `{x : x(g^(-1) h) = x(h) for all h ∉ F}`
  contains no cylinder: given a cylinder on a window `W`, pick `h ∉ F ∪ W ∪ gW`, which is possible because `Λ`
  is infinite. Then `g^(-1) h ≠ h`, and the letters at `h` and `g^(-1) h` can be chosen different.
- There are countably many pairs `(g, F)`.

**Lemma R′.** If `D >= R`, then `ψ(w) = I` for every relator `w`, so `ψ` is a homomorphism `Γ -> GL(W)`.

*Proof.* Fix `c ∈ C_0` and `z ∈ Λ`, and put `K = z^(-1) B_D`.
1. **Standard form on the window.** Any two sites of `K` are at distance `<= 2D`. By (T1) and (T2), the
   operators `E_(ab)(q)`, `q ∈ K`, give a unital homomorphism `⊗_(q ∈ K) M_A(k) = M_(A^K)(k) -> End(W_0)`. The
   source is simple, so this is injective. So `W_0 ≅ k^(A^K) ⊗ W'`, with `E_(ab)(q)` acting as `e^(q)_(ab) ⊗ I`.
   Here `e^(q)_(ab) δ_α = δ_(α[q := a])` if `α(q) = b`, and `0` otherwise, for `α ∈ A^K`.
2. **Transport map.** For `α ∈ A^K`, let `x*_α` be `x*` with its letters on `K` replaced by `α`. Put
   `β(c', z', α) = (c', z'.(y*, x*_α)) ∈ C × X`.
3. **One step.** Let `|μ| <= tℓ` with `t < n`, and let `σ ∈ Σ`. Apply `ψ(σ)` to
   `δ_(c') ⊗ δ_(μz) ⊗ δ_(α') ⊗ w'`.
   - The operators used sit at sites `(μz)^(-1) F_i ⊆ z^(-1) B_(tℓ + r) ⊆ K`.
   - The term for `i` is nonzero iff `c' ∈ [u_i]`, `y*((μz)^(-1) f) = π_(i,B)(f)` and
     `α'((μz)^(-1) f) = π_(i,A)(f)` for `f ∈ F_i`. That says `β(c', μz, α') ∈ [u_i] × [π_i]`, so exactly one
     `i` contributes.
   - That term is `δ_(v_i w) ⊗ δ_(λ_i μ z) ⊗ δ_(α'') ⊗ w'`, where `α''` is `α'` rewritten to `π_i'` on
     `(μz)^(-1) F_i`.
   - In `C × X`, rewriting `μz.ξ` on `F_i` is `μz.(ξ` rewritten on `(μz)^(-1) F_i)`. So
     `σ(β(c', μz, α')) = β(v_i w, λ_i μ z, α'')`.

   So `ψ(σ)` maps these basis vectors to basis vectors and is transported from `σ` through `β`, as long as
   the word stays within `n` letters.
4. **Relators.** For a relator `w`, iterating gives
   `ψ(w)(δ_c ⊗ δ_z ⊗ δ_α ⊗ w') = δ_(c') ⊗ δ_(z') ⊗ δ_(α') ⊗ w'`, with
   `β(c', z', α') = w.β(c, z, α) = β(c, z, α)`, since `w = 1` in `Γ ≤ F(T')`.
   - So `c' = c` and `g.x*_(α') = x*_α` for `g = z^(-1) z'`.
   - Both are finite modifications of `x*`, so `g.x*` and `x*` differ at finitely many sites. The choice of
     `x*` forces `g = 1`, and then `α' = α`.

   The vectors `δ_c ⊗ δ_z ⊗ δ_α ⊗ w'` span `δ_c ⊗ δ_z ⊗ W_0`, so `ψ(w) = I`. The relators `σσ^(-1)` make
   each `ψ(σ)` invertible. `∎`

## 2. Commutation

Let `D >= R`, let `E` be a `D`-tape family, and fix `p, q ∈ Λ` and `a, b ∈ A`. As in the source, put
`g_1 = t_(p^(-1))^(-1) e_a t_(p^(-1))` and `g_2 = t_(q^(-1))^(-1) e_b t_(q^(-1))`. Here `t_g` is a word in the
`t_s`.
- **They commute in `F(T')`.** Both fix the `X` coordinate and act on `C` by powers of `h` chosen by tape
  letters: `g_1(c, ξ) = (h^([x(p) = a]) c, ξ)`.
- **Their images.** Summing the tuples of `e_a` over `B`-letters and using (T1),
  `ψ(e_a)(δ_c ⊗ δ_z ⊗ u) = δ_(hc) ⊗ δ_z ⊗ E_(aa)(z^(-1)) u + δ_c ⊗ δ_z ⊗ (I - E_(aa)(z^(-1))) u`.
  So on the invariant subspace `k[C_0] ⊗ δ_1 ⊗ W_0`:
  `ψ(g_1) = I + (H - 1) ⊗ E_(aa)(p)` and `ψ(g_2) = I + (H - 1) ⊗ E_(bb)(q)`.
- **Conclusion.** By Lemma R′ the images commute. So `(H - 1)^2 ⊗ [E_(aa)(p), E_(bb)(q)] = 0`. The coefficient
  of `δ_(0^∞)` in `(H - 1)^2 δ_(0^∞)` is `1` in every characteristic, so `[E_(aa)(p), E_(bb)(q)] = 0`.

**So:** if `Γ` is finitely presented, then for `D >= R` the diagonal idempotents of every `D`-tape family
commute globally.

## 3. Slot families: proof of the theorem

Fix `D >= R`.
1. **Colouring.** The graph on `Λ` with edges `{q, q'}` for `0 < d(q, q') <= 2D` has degree `< m := |B_(2D)|`.
   Colouring greedily along an enumeration of `Λ` gives a proper colouring `κ : Λ -> {1, ..., m}`.
2. **A repeated colour.** `Λ` is infinite, so some `p ≠ q` have `κ(p) = κ(q)`.
3. **A rotation.** Fix letters `a_0 ≠ a_1` and let `T_0 ∈ GL(k^A)` send `δ_(a_1)` to `δ_(a_0) + δ_(a_1)` and fix
   the other basis vectors.
4. **The family.** Put `W_0 = (k^A)^(⊗ m)`. Let `E_(ab)(s)` act on tensor slot `κ(s)` by
   `g_s e_(ab) g_s^(-1)`, and as the identity on the other slots. Here `g_q = T_0` and `g_s = I` for `s ≠ q`.
5. **It is a tape family.** (T1) holds because conjugated matrix units are matrix units. (T2) holds because
   distinct sites within `2D` have distinct colours, so they act on different slots.
6. **It does not commute.** `E_(a_0 a_0)(p) = e_(a_0 a_0)` and `P' = E_(a_0 a_0)(q) = T_0 e_(a_0 a_0) T_0^(-1)`
   act on the same slot. On it, `P' δ_(a_1) = -δ_(a_0)`, so `e_(a_0 a_0) P' δ_(a_1) = -δ_(a_0)` while
   `P' e_(a_0 a_0) δ_(a_1) = 0`. They do not commute, in any characteristic.

This contradicts Section 2, so no finitely presented `Γ` exists. `∎`

## 4. Corollaries

**Minimality and simplicity (`Y` a point).**
- **Minimal.** The `𝒯`-orbit of `x` contains every finite modification of `x`, which is dense in `A^Λ`. `G_V`
  is minimal, and a product of minimal groupoids is minimal.
- **Effective.** Let `U` be an open bisection of `𝒯` lying in the isotropy. Shrink it to `{(λ, ρ(x), x) : x ∈ W}`.
  - If `λ ≠ 1`, then `λ.x` and `x` differ at finitely many sites for every `x ∈ W`. The Baire argument of
    Section 1 shows that such points form a meagre set, which cannot contain the open set `W`.
  - If `λ = 1`, then `ρ` is the identity on `W`.

  So `U` consists of units. Isotropy of a product is the product of isotropies, so `T'` is effective too.
- **Simple.** `A(T')` is simple by Theorem 4.1 of `nekrashevych-symmetric-and-alternating-full-groups`, and
  `F(T') = A(T')` by `v-times-ample-full-groups-are-generated-by-transpositions`.

**Finite generation (sketch).**
- **A cover.** Cover the compact generating set of `𝒯` by bisections: the `t_s` and the involutions swapping
  two letters at the origin, each restricted to origin cylinders.
- **Expansive.** Conjugating by translations moves cylinders and rewrites to any site. Products give every
  window rewrite, followed by a translation and restricted to a cylinder, so the products of the cover form a
  basis of `𝒯`. So `𝒯` is expansive.
- **Conclusion.** `T'` is expansive by `ample-groupoid-products-expansive-iff-factors-are`, its orbits are
  infinite, and Theorem 5.6 of the import makes `A(T')` finitely generated.

**Corollary 2.** Put `Λ = Z`, `A = {0,1}` and `x ↦ (x(1) x(2) ..., x(0) x(-1) ...)`, which identifies `A^Z` with
`C × C`.
- **Translation.** `t_1` moves the first letter of the second coordinate to the front of the first: it is the
  baker's map, with length changes `(+1, -1)`.
- **Rewrites.** A tape rewrite on a finite window replaces prefixes of equal length in both coordinates.
- **Conversely.** A germ `(u_1 z_1, u_2 z_2) ↦ (w_1 z_1, w_2 z_2)` with `|w_1| - |u_1| = |u_2| - |w_2| = j` is
  translation by `j` after a finite rewrite.

So `𝒯 ≅ {(g_1, g_2) ∈ G_V × G_V : c(g_1) + c(g_2) = 0}` as topological groupoids, since the basic bisections
correspond. Then `F(T') = 3V_□ ≤ F(G_V^3) = 3V`. The lamplighter is generated by `t_1` and the letter flip at
the origin.

## 5. The ring remark

Let `R_Λ = (⊗_Λ M_A(k)) ⋊ Λ`, generated by the units `u_s` and the matrix units `e_(ab)` at the origin. For a
tape family `E`, let `R_Λ` act on `k[Λ] ⊗ W_0`, with `u_s` shifting `δ_z` and `e_(ab)` acting at `δ_z` by
`E_(ab)(z^(-1))`.
- **Relators hold.** A relator of bounded length is a linear combination of monomials that only involve
  sites in a ball.
  - Step 1 of Lemma R′ puts the family in standard form on that ball.
  - Each monomial then maps `δ_z ⊗ δ_α ⊗ w'` to a basis vector or to `0`. It does so exactly as it acts on the
    basis vector `δ_(z.x*_α)` of the classical orbit module of `x*`, whose basis is the translates of finite
    modifications of `x*`.
  - The transport `δ_z ⊗ δ_α ⊗ w' ↦ δ_(z.x*_α) ⊗ w'` is injective by the choice of `x*`.
  - The orbit module is an `R_Λ`-module, so a relator acts there as `0`, and so also on `k[Λ] ⊗ W_0`.
- **A true relation fails.** `[e_(aa), u_g e_(bb) u_g^(-1)] = 0` holds in `R_Λ` for `g ≠ 1`, and it fails on the
  slot family of Section 3.

So `R_Λ` is not finitely presented. Here no `V` is needed, because the ring already contains the commutator of
idempotents.
