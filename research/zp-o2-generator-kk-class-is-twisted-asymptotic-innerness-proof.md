---
rg: 2
id: zp-o2-generator-kk-class-is-twisted-asymptotic-innerness-proof
kind: route
title: Compare the generator with the identity twisted by a scalar cocycle in Gabe--Szabó uniqueness, then split the action element by the Chinese remainder theorem over Z[zeta_p, 1/p]
target: zp-o2-generator-kk-class-is-twisted-asymptotic-innerness
requires:
  - gabe-szabo-unital-uniqueness-theorem
  - zp-algebras-with-contractible-restriction-are-cyclotomic
  - zp-restriction-trivial-splits-cellular-plus-phantom
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
  - zp-o2-contractible-crossed-product-only-coboundaries
---

**Conventions.**  Gabe--Szabó (arXiv:2205.04933v3, Section 1, as quoted in
`zp-o2-contractible-crossed-product-only-coboundaries-proof`) define
`KK^G(φ, u)` as the class of `(B^u, φ, 0)`, where `B^u` carries
`g·b = u_g β_g(b)`.
- For the scalar cocycle `u_g = ψ(g)1` on `E = (O_2, α)`, `B^ψ = C_ψ ⊗ O_2`.
  So `KK^G(id, ψ) = ψ·1_E`.
- `θ = KK^G(α_ω, 1)`.  `α_ω` is equivariant because `G` is abelian.
- Cyclotomic node items 1–3, used below:
  - `1 − χ` is invertible for every generating character `χ`;
  - `ρ = Σ_(χ∈Ĝ) χ` acts as `0`;
  - `p` is invertible.

**Standard inputs, not re-read.**
- (KP) A unital separable nuclear simple purely infinite algebra that is
  KK-contractible is `O_2`.  The crossed product of `O_2` by an outer action
  of a finite group is simple and purely infinite (Kishimoto).
- (IC) `KK^G` of separable `G`-algebras is triangulated with countable direct
  sums (Meyer–Nest), hence idempotent complete.  For an idempotent `e`, the
  homotopy colimit of `E →e E →e ⋯` is `eE`.  An inductive limit of a sequence
  of equivariant \*-homomorphisms is its homotopy colimit, via the mapping
  telescope.
- (AI) Every automorphism of `O_2` is approximately inner.

**Item 1.**  Apply Theorem 5.8 of `gabe-szabo-unital-uniqueness-theorem` with
`A = B = O_2` and `α = β`.  Its hypotheses are checked in
`zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner-proof`: `G` exact,
`α` amenable, and `α` isometrically shift-absorbing by Proposition 3.15.
- `(id, ψ)` is a unital cocycle embedding, because
  `Ad(ψ(g)) ∘ α_g ∘ id = id ∘ α_g`.  So is `(α_ω, 1)`.
- Their classes are `ψ·1_E` and `θ`.  They agree iff the embeddings are
  asymptotically unitarily equivalent.
- By Definition 1.15 with `(φ, u) = (id, ψ)` and `(ψ', v) = (α_ω, 1)`, that
  means a continuous unitary path `u_t` with `α_ω(a) = lim_t u_t a u_t^*` and
  `‖1 − u_t ψ(g) α_g(u_t)^*‖ → 0`.
- Multiplying on the right by the unitary `α_g(u_t)`, the second condition is
  `‖α_g(u_t) − ψ(g) u_t‖ → 0`.

**Item 4, first statement.**
- By item 1 of the splitting node, `θ^p = 1`, so `(1 − θ) Φ_p(θ) = 0`.  By
  item 2 there, `O_2 ⋊_α G ≃_KK 0` iff `1 − θ` is invertible.
- If `1 − θ` is invertible, `Φ_p(θ) = 0`.
- Conversely, suppose `Φ_p(θ) = 0`.  Then `Z[1/p][θ]` is a quotient of
  `Z[1/p][y]/Φ_p(y) = Z[ζ_p, 1/p]`.  There
  `p = ∏_(k=1)^(p−1) (1 − ζ^k)`, and
  `1 − ζ^k = (1 − ζ)(1 + ⋯ + ζ^(k−1))`, so `1 − ζ` divides `p`.  Hence
  `1 − ζ` is a unit, and `1 − θ` is invertible.

**Item 2.**
- By item 1, `θ = ψ·1_E`.  Since `ψ ≠ 1` generates `Ĝ`,
  `Φ_p(θ) = Σ_m ψ^m·1_E = ρ·1_E = 0`.
- By item 4, `O_2 ⋊_α G ≃_KK 0`, and by (KP) it is `O_2`.

**Item 3.**
- **Rokhlin ⟹ all twists.**  By item 2 of
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, Rokhlin gives `E ≃ 0`.
  So `θ = ψ·1_E` for every `ψ`, and item 1 gives every twist.
- **Two twists ⟹ Rokhlin.**  If `ψ·1_E = θ = ψ'·1_E` with `ψ ≠ ψ'`, then
  `(1 − ψ'ψ̄)·1_E = 0`.  `ψ'ψ̄` is a generating character, so `1 − ψ'ψ̄` is
  invertible and `1_E = 0`.  By item 2 of that node, `α` is Rokhlin.

**Item 4, components.**
1. **Algebra structure.**
   - `χ·1_E` is central in `S = KK^G(E, E)`, because exterior products with
     `R(G)` commute with Kasparov products.  `θ` is central by naturality
     (splitting item 1).
   - `Φ_p(χ) = ρ` acts as `0`, `Φ_p(θ) = 0`, and `p` is invertible.  So `S` is
     an algebra over
     `R = Z[1/p][x, y]/(Φ_p(x), Φ_p(y)) = Z[ζ_p, 1/p][y]/Φ_p(y)`.
   - Over `Z[ζ_p, 1/p]`, `Φ_p(y) = ∏_(k ∈ F_p^×) (y − ζ^k)`.  For `j ≠ k`,
     `ζ^j − ζ^k = ζ^j(1 − ζ^(k−j))` is a unit.
   - By the Chinese remainder theorem, `R ≅ ∏_k Z[ζ_p, 1/p]`, with `y ↦ ζ^k`
     in factor `k`.  The idempotents
     `e_k = ∏_(j≠k) (y − x^j)/(x^k − x^j)` satisfy `Σ e_k = 1`,
     `e_j e_k = 0` for `j ≠ k`, and `(y − x^k) e_k = 0`.
2. **Splitting.**  By (IC), `E ≅ ⊕_k E_k` with `E_k = e_k E`.  Here `θ = χ^k`,
   because `(θ − χ^k) e_k = 0`.
3. **Realization.**
   - By item 3 of `zp-o2-contractible-crossed-product-only-coboundaries`,
     `e_k` is the class of a unital equivariant endomorphism `φ_k` of
     `(O_2, α)`.
   - The limit `lim(O_2 →φ_k O_2 →φ_k ⋯)`, with the limit action, is a
     separable nuclear `G`-algebra.  By (IC) it represents `E_k`.
   - `Res E_k` and `E_k ⋊ G` are retracts of `Res E ≃ 0` and `E ⋊ G ≃ 0`.
   - By item 3 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, `E_k` is
     KK^G-equivalent to a pointwise outer `α^(k)` on unital `O_2` with
     contractible crossed product.
   - By naturality of `θ` and `R(G)`-linearity of the equivalence, `θ = χ^k`
     for `α^(k)`.  Item 1 then gives `χ^k`-twisted asymptotic innerness.
   - If `α^(k)` were also `1`-twisted, `(1 − χ^k)·1 = 0` would force
     `E_k ≃ 0`.

**Item 5.**
- **(⟹)** Let `α` be `χ^k`-twisted with `k ≠ 0`.  By item 2 the crossed
  product is contractible.  Detection for `D = (O_2, α)` gives `E ≃ 0`, so
  `θ = 1`, and item 1 with `ψ = 1` gives invariant asymptotic innerness.
- **(⟸)** Let `D` be separable nuclear with `Res D ≃ 0` and `D ⋊ G ≃ 0`.
  1. By item 3 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, `D` is
     KK^G-equivalent to an outer `(O_2, α)` with contractible crossed product.
  2. By item 4, `E = ⊕ E_k`, with each `E_k` realized by a `χ^k`-twisted
     `α^(k)`.
  3. The hypothesis makes each `α^(k)` invariantly asymptotically inner, so
     `θ = 1` on `E_k`.  Together with `θ = χ^k`, this gives `E_k ≃ 0`.
  4. Hence `D ≃ 0`.

**Item 6.**  `Ĝ = {1, χ}` with `χ(ω) = −1`.  Odd paths are the `χ`-twisted
ones, even paths the `1`-twisted ones.
- **Crossed product.**  If it is contractible, `Φ_2(θ) = 1 + θ = 0` and
  `1 + χ = ρ` acts as `0`.  So `θ = −1 = χ·1_E`, and item 1 gives an odd path.
  The converse is item 2.
- **Rokhlin.**  Item 3 with `ψ = χ` and `ψ' = 1`.
- **Detection.**  Item 5 with `k = 1`.

**Item 7.**
- **Existence of `v`.**  (AI) gives `v`.  On a component with `θ = χ^k`, take
  instead `v = [(u_(t_n))_n]` from the path of item 1, with `t_n → ∞`.  Then
  `v^* α_g(v) = χ^k(g)` holds exactly in `A_∞`.
- **Cocycle.**  `α_g(v)` implements `α_g α_ω α_g^(−1) = α_ω` on `A`, so
  `w_g = v^* α_g(v)` commutes with `A`.  Also
  `w_(g+h) = w_g α_g(w_h)`.
- **Independence.**  If `v' = v z`, then `z = v^* v'` commutes with `A`.  So
  `z ∈ U(F_∞(A))` and `v'^* α_g(v') = z^* w_g α_g(z)`.
- **Triviality of the scalar class.**  The class of `χ^k` is trivial iff some
  `z ∈ U(F_∞(A))` has `α_g(z) = χ̄^k(g) z`.  By item 2 the crossed product is
  `O_2`, so by item 5 of
  `zp-o2-contractible-crossed-product-only-coboundaries` this holds iff
  `α` is Rokhlin.
