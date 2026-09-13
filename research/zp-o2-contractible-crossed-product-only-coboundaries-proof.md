---
rg: 2
id: zp-o2-contractible-crossed-product-only-coboundaries-proof
kind: route
title: Theorem 5.14 decides coboundaries by the unit class, Theorem 5.6 realizes classes by cocycle embeddings that then untwist, and Izumi's theorem on the dual action converts central eigen-unitaries into Rokhlin towers
target: zp-o2-contractible-crossed-product-only-coboundaries
requires:
  - gabe-szabo-asymptotic-coboundary-kk-criterion
  - gabe-szabo-unital-uniqueness-theorem
  - izumi-rokhlin-approximately-representable-duality
  - o2-contractible-crossed-product-inner-half-flip-mcduff
---

**Sources.**
- Gabe--Szabó arXiv:2205.04933v3, read on MSI 2026-09-13:
  - Theorem 5.14 and Corollary 5.11, quoted in
    `gabe-szabo-asymptotic-coboundary-kk-criterion-citation`;
  - Proposition 3.15, quoted in `gabe-szabo-unital-uniqueness-theorem-citation`.
- **Theorem 5.6**, verbatim: "Suppose G is exact. Let A be a separable exact
  unital C∗-algebra with an action α : G ↷ A. Let B be a unital Kirchberg
  algebra and β : G ↷ B an amenable and isometrically shift-absorbing action.
  Then for every x ∈ KK^G(α, β) with [1_A]_0 ⊗ x = [1_B]_0 ∈ K_0(B), there
  exists a unital cocycle embedding (ψ, v) : (A, α) → (B, β) such that
  KK^G(ψ, v) = x."
- **Section 1 of the same paper**, as printed before Proposition 1.12.
  - For a cocycle morphism `(φ, u)`, `B^u` is `B` as a right Hilbert module,
    with `G`-action `g·b := u_g β_g(b)`.
  - "one defines KK^G(φ, u) ∈ KK^G(α, β)" as the class of the Kasparov
    triple `(B^u, φ, 0)`.

**Standard inputs, not re-read.**
- (GJ) Green--Julg: for finite `G`, `KK^G(C, B) ≅ K_0(B ⋊ G)`.  It sends
  `KK^G(ι_B)` to the class of `|G|^(−1) Σ_g u_g`.
- (IR) Induction–restriction: `KK^G(C(G), E) ≅ KK(C, Res E)`.
- (RC) If `α` is a pointwise outer action of a finite group on a simple unital
  algebra `A`, then `A' ∩ (A ⋊_α G) = C` (Kishimoto).
- Actions of finite groups are amenable, and finite groups are exact.
- Convention: a cocycle morphism satisfies `φ ∘ α_g = Ad(u_g) ∘ β_g ∘ φ`.  The
  opposite convention only replaces `v` by `v^*` below.

**Item 1.**  `β` is amenable, and isometrically shift-absorbing by Proposition
3.15.  `G` is exact and `B` is unital.  So Theorem 5.14(ii) says: `w` is an
asymptotic coboundary iff `w^♯ = KK^G(ι_B)`.
- By Corollary 5.11 an asymptotic coboundary is a coboundary.
- Conversely, a coboundary is an asymptotic coboundary along the constant
  path.

**Item 2.**
- **(⟹)** If `φ` is a unital equivariant \*-homomorphism with class `x`, then
  `[1_A]_0 ⊗ x = [φ(1)]_0 = [1_B]_0`, and
  `KK^G(ι_A) ⊗ x = KK^G(φ ∘ ι_A) = KK^G(ι_B)`.
- **(⟸)** Theorem 5.6 gives a unital cocycle embedding `(φ, w)` with
  `KK^G(φ, w) = x`.
  - The Kasparov product of the \*-homomorphism class `KK^G(ι_A)` with the
    triple `(B^w, φ, 0)` is `(B^w, φ ∘ ι_A, 0) = (B^w, ι_B, 0)`, which is
    `w^♯`.
  - So the hypothesis gives `w^♯ = KK^G(ι_B)`, and by item 1
    `w_g = v β_g(v)^*` for a unitary `v`.
  - Put `φ' = Ad(v^*) ∘ φ`.  From `β_g(φ(a)) = w_g^* φ(α_g(a)) w_g` and
    `w_g = v β_g(v)^*` we get
    `β_g(φ'(a)) = β_g(v)^* β_g(φ(a)) β_g(v) = v^* φ(α_g(a)) v = φ'(α_g(a))`.
    So `φ'` is equivariant, unital, and injective since `φ` is.
  - `T(b) = v^* b` is a unitary isomorphism of Hilbert modules
    `B^w → B`.  It satisfies `T(φ(a)b) = φ'(a)T(b)` and
    `T(w_g β_g(b)) = β_g(v)^* β_g(b) = β_g(T(b))`.  So `(B^w, φ, 0)` and
    `(B, φ', 0)` are isomorphic triples, and `KK^G(φ') = x`.

**Item 3.**
- By (GJ), `KK^G(C, E) ≅ K_0(O_2 ⋊_β G) = 0`.  So `w^♯ = 0 = KK^G(ι_B)` for
  every cocycle, and item 1 applies.
- If `w_g = v β_g(v)^*`, then `β^w_g = Ad(w_g) β_g = Ad(v) ∘ β_g ∘ Ad(v^*)`, a
  conjugate action.
- For abelian `G` and `ψ ∈ Ĝ`, the scalars `ψ(g)1` form a cocycle, since they
  are fixed and multiplicative.  A coboundary `ψ(g) = v β_g(v)^*` gives
  `β_g(v) = ψ̄(g) v`.  Apply this to `ψ̄` to get eigenvalue `ψ`.
- For `x ∈ KK^G(A, E)`: `[1_A]_0 ⊗ x ∈ K_0(O_2) = 0 = [1]_0`, and
  `KK^G(ι_A) ⊗ x ∈ KK^G(C, E) = 0 = KK^G(ι_(O_2))`.  So item 2 realizes `x`.
  For `A = O_2` this realizes every element of `KK^G(E, E)`.

**Item 4.**  Write `E = (O_2, β)`, and recall `K_0(O_2) = 0`.
- **(i ⟹ iii).**  For `(A, α)` take `x = 0 ∈ KK^G(A, E)`.  Then
  `[1_A]_0 ⊗ x = 0 = [1]_0`, and `KK^G(ι_A) ⊗ x = 0 = KK^G(ι_(O_2))` by (i).
  Item 2 gives the embedding.
- **(iii ⟹ ii).**  Take `A = C(G)` with left translation.  The towers `e_g`
  are the images of the `δ_g`.
- **(ii ⟹ i).**  Let `φ : C(G) → O_2` be unital and equivariant.  Then
  `KK^G(ι_(O_2)) = KK^G(ι_(C(G))) ⊗ KK^G(φ)`, and
  `KK^G(φ) ∈ KK^G(C(G), E) ≅ KK(C, O_2) = 0` by (IR).

**Item 5.**
- **(⟹)** Rokhlin projections `e_g ∈ F_∞(O_2)`, as in Barlak--Li
  Definition 2.6 quoted in `izumi-rokhlin-approximately-representable-duality`,
  satisfy `Σ e_g = 1` and `α_h(e_g) = e_(h+g)`.  Put `w = Σ_g ψ̄(g) e_g`.  Then
  `α_h(w) = Σ_g ψ̄(g − h) e_g = ψ(h) w`.
- **(⟸)** Lift `w` to unitaries `w_n ∈ O_2`: lift arbitrarily and take polar
  parts.  Then `[w_n, a] → 0` and `‖α_g(w_n) − ψ(g) w_n‖ → 0`.
  1. Let `B = O_2 ⋊_α G`, generated by `A = O_2` and unitaries `u_g`.  The dual
     action is `α̂_χ(a u_g) = χ(g) a u_g`, with fixed-point algebra `A`.
  2. `Ad(w_n)(a) → a`, and
     `Ad(w_n)(u_g) = w_n α_g(w_n)^* u_g → ψ̄(g) u_g = α̂_(ψ̄)(u_g)`.
     So `α̂_(ψ̄) = lim_n Ad(w_n)` pointwise, with `w_n ∈ B^(α̂)`.
  3. `ψ̄` generates `Ĝ ≅ Z/p`, and `Ad(w_n^m) → α̂_(ψ̄^m)`.  So `α̂` is strongly
     approximately inner, Barlak--Li Definition 4.13.
  4. **`α̂` is pointwise outer.**  Suppose `α̂_χ = Ad(z)` with `z ∈ U(B)`.  Then
     `z` commutes with `A`, so `z ∈ A' ∩ B = C` by (RC), and `χ = 1`.
  5. `B ≅ O_2` by hypothesis.  Item 3 of
     `izumi-rokhlin-approximately-representable-duality` (Izumi I,
     Theorem 4.6, prime-power order) makes `α̂` approximately representable.
     By item 2 there (Barlak--Li Theorem 2.8), `α` has the Rokhlin property.

**Item 6.**
- **(⟸)** Let `ι : (S, γ) → (F_∞(O_2), α_∞)` be unital and equivariant.
  1. `1 − ψ̄ = (1 − ψ)(1 + ψ + ⋯ + ψ^(p−2))`, so `(1 − ψ̄)·KK^G(ι_S) = 0` as
     well.
  2. The scalar cocycle `ψ̄` has `ψ̄^♯ = KK^G(ι_S, ψ̄)`, the class of
     `(S^(ψ̄), ι_S, 0)`.  Since `S^(ψ̄) = C_(ψ̄) ⊗ S`, this is
     `ψ̄·KK^G(ι_S) = KK^G(ι_S)`.
  3. Item 1, for the unital Kirchberg algebra `S` with outer action `γ`, gives
     `v ∈ U(S)` with `γ_g(v) = ψ(g) v`.
  4. `ι(v)` is then a unitary eigenvector in `F_∞(O_2)` with nontrivial
     eigenvalue, and item 5 gives the Rokhlin property.
- **(⟹)** By item 3 of `o2-contractible-crossed-product-inner-half-flip-mcduff`,
  a Rokhlin `α` admits a unital equivariant
  `(O_2, α) → (A_∞ ∩ O_2', α_∞)`.  Take `S = O_2` and `γ = α`.  By (GJ),
  `KK^G(C, S) = K_0(O_2 ⋊_α G) = 0`, so the condition holds.

**Model tests** are in the claim.  Item 4 is the equivariant form of the
remark in `o2-contractible-crossed-product-inner-half-flip-mcduff` that
`[ι_D]` is the class of the averaging projection.
