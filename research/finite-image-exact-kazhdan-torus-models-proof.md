---
rg: 2
id: finite-image-exact-kazhdan-torus-models-proof
kind: route
title: A wrap of defect below the Kazhdan constant forces equal supports, hence an exact multiplicity-free wrap and an isometric stage automorphism; the Frobenius core of the 1/2-ball is abelian, normal and invariant, and dividing by it yields stage lifts
target: finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts
requires:
  - fpbs-shalom-property-t-is-open
  - lef-mapping-torus-iff-stage-liftable-automorphism
  - lef-implies-operator-mf
artifacts:
  - research/thompson-gap-witnesses-need-nonamenable-image-proof.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
---

The notation is that of the target claim. All norms on matrices are operator norms unless marked `HS`
(Hilbert–Schmidt). We write `[g,h] = g h g^-1 h^-1`. For a finite-dimensional unitary representation `U` of `F`,
`Supp U` is its finite set of irreducible constituents, up to equivalence.

Imports, used verbatim:
- `fpbs-shalom-property-t-is-open`: a finitely generated Kazhdan group `K = <S | R>` has a finite
  `R_0 ⊆ R` with `<S | R_0>` Kazhdan.
- `lef-mapping-torus-iff-stage-liftable-automorphism`, (a) ⇔ (b): "`G` is LEF" iff "some sequence of
  **finite** marked groups `(F_i, S)` converges to `(K, S)`, and every `F_i` carries a stage lift `α_i` of `φ`",
  where a stage lift means `α_i(π_i(s)) = π_i(w_s)` for every `s ∈ S`. No hypothesis on `K` beyond finite
  generation is used.
- `lef-implies-operator-mf`: "Every countable LEF group is operator MF, in the norm-matrix-corona sense".

## Frobenius lemmas

**F1.** For unitaries `A, B`: `‖[A,B] - 1‖ ≤ 2 ‖A - 1‖ ‖B - 1‖`.

*Proof.* `[A,B] - 1 = (AB - BA) A^-1 B^-1` and `AB - BA = (A-1)(B-1) - (B-1)(A-1)`.

**F2.** Let `A, B` be unitaries with `‖B - 1‖ < √2`. If `A` commutes with `B A B^-1`, then `AB = BA`.

*Proof.*
1. Write `A = Σ_λ λ P_λ` (spectral projections) and `Q_μ = B P_μ B^-1`. Since `A` and `BAB^-1` are commuting
   normal operators, every `P_λ` commutes with every `Q_μ`.
2. Suppose `λ ≠ μ` and `x` is a unit vector in `Ran P_λ ∩ Ran Q_μ`. Put `y = B^-1 x ∈ Ran P_μ`. Then `By = x`
   is orthogonal to `y`, since `Ran P_λ ⊥ Ran P_μ`. So `‖By - y‖ = √2`, contradicting `‖B - 1‖ < √2`.
3. Since `Q_μ` commutes with all `P_λ`, `Ran Q_μ = ⊕_λ (Ran P_λ ∩ Ran Q_μ) = Ran P_μ ∩ Ran Q_μ`. So
   `Ran Q_μ ⊆ Ran P_μ`. The ranks are equal, so `Q_μ = P_μ` for all `μ`. Hence `BAB^-1 = A`.

**F3.** Let `Γ ≤ U(n)` be a finite group, and let `A, B ∈ Γ` with `a = ‖A - 1‖ < 1/2` and `b = ‖B - 1‖ < √2`.
Then `AB = BA`.

*Proof.*
1. Put `B_0 = B` and `B_(k+1) = [A, B_k] ∈ Γ`. By F1, `‖B_k - 1‖ ≤ (2a)^k b ≤ b`.
2. Let `μ = min{‖g - 1‖ : g ∈ Γ, g ≠ 1} > 0`. Since `2a < 1`, some `N` has `(2a)^N b < μ`, so `B_N = 1`.
3. Back-tracking. Suppose `A` commutes with `B_(k+1) = A · (B_k A^-1 B_k^-1)`. Then `A` commutes with
   `B_k A^-1 B_k^-1`, hence with its inverse `B_k A B_k^-1`. Since `‖B_k - 1‖ ≤ b < √2`, F2 gives
   `A B_k = B_k A`.
4. Descending from `B_N = 1` gives `AB = BA`.

These are Lemmas 1 and 2 of `thompson-gap-witnesses-need-nonamenable-image-proof`, reproved here. F3 needs
finiteness only in step 2.

**F4 (Kazhdan abelian quotients).** Every abelian quotient of a finitely generated Kazhdan group is finite.

*Proof.* It is a finitely generated abelian Kazhdan group, since property (T) passes to quotients. If it were
infinite, it would surject onto `Z`. The characters `χ_θ(n) = e^(inθ)` of `Z`, as `θ -> 0`, have almost
invariant vectors and no invariant vector in their direct sum. This contradicts (T) for `Z`.

## Proof of Theorem A

Let `U : F -> U(n)` be an exact model, `T ∈ U(n)`, and `δ = max_s ‖T U(s) T* - U(w_s)‖ < κ`.

**Step A1 (two representations of `K~`).**
- `U` kills `R_0 ⊆ R_Γ`, so every `σ ∈ Supp U` factors through `K~`.
- `U ∘ ŵ` kills `R_0`, because `ŵ(R_0) ⊆ R_Γ`. So `U ∘ ŵ`, and every `τ ∈ Supp(U∘ŵ)`, factors through `K~`.

**Step A2 (`Supp U ⊆ Supp(U∘ŵ)`).**
1. Fix `σ ∈ Supp U` on `H_σ`, and an isometry `J : H_σ -> C^n` with `U(g) J = J σ(g)`.
2. On the Hilbert–Schmidt space `HS(H_σ, C^n)`, put `W(g) X = U(ŵ g) X σ(g)*`. By A1 this is a unitary
   representation of `K~`.
3. Put `X = T J`, so `‖X‖_HS = ‖J‖_HS > 0`. Using `T J = T U(s) J σ(s)*`,

   ```text
   W(s)X - X = (U(w_s) T - T U(s)) J σ(s)*,    ‖W(s)X - X‖_HS ≤ δ ‖J‖_HS = δ ‖X‖_HS.
   ```

4. Since `δ < κ`, `W` has a nonzero invariant vector `X_0`. That is, `U(ŵ g) X_0 = X_0 σ(g)`: `X_0` is a
   nonzero intertwiner from `σ` to `U∘ŵ`. By Schur, `X_0* X_0` is a positive scalar, so `σ ⊂ U∘ŵ`.

**Step A3 (`Supp(U∘ŵ) ⊆ Supp U`).**
- Fix `τ ∈ Supp(U∘ŵ)` with an isometry `J'`, `U(ŵ g) J' = J' τ(g)`.
- Put `W'(g) X = U(g) X τ(g)*`, a representation of `K~` by A1, and `X = T* J'`.
- Then `W'(s)X - X = (U(s) T* - T* U(w_s)) J' τ(s)*`, and `‖U(s)T* - T*U(w_s)‖ = ‖T U(s) T* - U(w_s)‖ ≤ δ`.
  Conclude as in A2.

**Step A4 (the automorphism α).**
1. `ker U = ∩_(σ ∈ Supp U) ker σ` and `ker(U∘ŵ) = ∩_(τ ∈ Supp(U∘ŵ)) ker τ`. By A2 and A3 the index sets are
   equal, so `U(x) = 1 ⇔ U(ŵ x) = 1`.
2. So `α(U(x)) = U(ŵ x)` is a well-defined injective endomorphism of `M = U(F)`.
3. `r_s ∈ R_Γ` gives `U(s) = U(ŵ v_s) = α(U(v_s))`. So `α` is onto, and it is an automorphism of `M`. This is
   item 2.

**Step A5 (exact wrap).**
1. Each `σ ∈ Supp U` is `σ̄ ∘ U` for an irreducible representation `σ̄` of the group `M`. Then
   `σ ∘ ŵ = σ̄ ∘ α ∘ U`, and it is irreducible because `α` is an automorphism.
2. `σ ↦ σ∘ŵ` is injective on classes: `σ̄∘α ≅ σ̄'∘α` implies `σ̄ ≅ σ̄'`.
3. `U∘ŵ ≅ ⊕_σ m_σ (σ∘ŵ)`, so `Supp(U∘ŵ) = {σ∘ŵ : σ ∈ Supp U}`. By A2 and A3 this equals `Supp U`. So
   `σ ↦ σ∘ŵ` is a permutation of the finite set `Supp U`.
4. Hence `U♭ ∘ ŵ = ⊕_σ σ∘ŵ ≅ ⊕_σ σ = U♭`. Any unitary intertwiner `V` gives `V U♭(x) V* = U♭(ŵ x)` for all
   `x ∈ F`. This is item 3.

**Step A6 (norms).**
- For `a ∈ C[F]`, `‖U(a)‖ = max_(σ ∈ Supp U) ‖σ(a)‖ = ‖U♭(a)‖`, since multiplicities do not change operator
  norms. This is item 1.
- For `m = U(x)`: `‖α(m) - 1‖ = ‖U♭(ŵ x) - 1‖ = ‖V (U♭(x) - 1) V*‖ = ‖U(x) - 1‖`. This is item 4. ∎

Nothing here uses finiteness of `M`.

## Proof of Corollary A

1. `δ_i = max_s ‖T_i U_i(s) T_i* - U_i(w_s)‖ -> 0`, because `π(t)π(s)π(t)* = π(φ(s))`. So `δ_i < κ` for large
   `i`, and Theorem A gives `U♭_i` and `V_i`. Finitely many stages are irrelevant in the corona.
2. For every relator `r` of `K`, `‖U♭_i(r) - 1‖ = ‖U_i(r) - 1‖ -> 0` by A6. So `s ↦ [U♭_i(s)]` defines a
   homomorphism of `K`.
3. `V_i U♭_i(s) V_i* = U♭_i(w_s)` exactly, so `π♭(t) π♭(s) π♭(t)* = π♭(φ(s))`.
4. `G = < S, t | relators of K, t s t^-1 = w_s >` presents `K ⋊_φ Z`, because `φ` is an automorphism. So `π♭`
   is a homomorphism of `G`.
5. For a word `x` representing `k ∈ K`, `‖U♭_i(x) - 1‖ = ‖U_i(x) - 1‖` at every stage. So
   `‖π♭(k) - 1‖ = ‖π(k) - 1‖`.
6. At every large stage, `(U♭_i, V_i)` satisfies `R_Γ` and `t s t^-1 = w_s` exactly. So it is a representation
   of `G_Γ`. ∎

## Proof of Theorem B

Let `M_i` be finite for all large `i`, and let `α_i ∈ Aut(M_i)` be as in Theorem A. Let `π_i : F -> F_i = M_i/A_i`
be `U_i` followed by the quotient map.

**B1 (the core).**
- By F3 with `b < 1/2 < √2`, any two elements of `E_i` commute. So `A_i = <E_i>` is abelian.
- `E_i` is closed under conjugation in `M_i ⊂ U(n_i)`, because unitary conjugation preserves norms. So `A_i`
  is normal.
- `α_i` is an isometry (A6), so `α_i(E_i) = E_i` and `α_i(A_i) = A_i`. This is item 1.

**B2 (stage lifts).** `α_i` descends to `ᾱ_i ∈ Aut(F_i)`. Then
`ᾱ_i(π_i(s)) = [α_i(U_i(s))] = [U_i(w_s)] = π_i(w_s)`. This is item 2.

**B3 (relators).** For a relator `r` of `K`, `‖U_i(r) - 1‖ -> 0`. So eventually `U_i(r) ∈ E_i ⊆ A_i`. This is
item 3.

**B4 (dichotomy).**
1. Let `x_k ∈ F` represent `k`. Since `π(k) ≠ 1`, there are `ε > 0` and an infinite `J_0` with
   `‖U_i(x_k) - 1‖ ≥ ε` for `i ∈ J_0`. Then `π_J(k) ≠ 1` for every infinite `J ⊆ J_0`.
2. `F` is countable, so a diagonal argument gives an infinite `J_1 ⊆ J_0` such that, for every `u ∈ F`, either
   `π_i(u) = 1` for all large `i ∈ J_1`, or `π_i(u) ≠ 1` for all large `i ∈ J_1`. Let `N_F` be the set of `u`
   of the first kind. It is a normal subgroup of `F`, and by B3 it contains every relator of `K`. Let `N` be
   its image in `K`.
3. `N` is `φ`-invariant. By B2, `π_i(ŵ u) = ᾱ_i(π_i(u))`, and `ᾱ_i` is injective. So `u ∈ N_F ⇔ ŵ u ∈ N_F`.
   Since `ŵ u` represents `φ(ū)`, this says `k' ∈ N ⇔ φ(k') ∈ N`.
4. `(F_i, S)_(i ∈ J_1)` is a sequence of finite marked groups converging to `(K/N, S)`. Each carries the stage
   lift `ᾱ_i` of the induced automorphism `φ̄` of `K/N`, with the same words `w_s`. By the imported criterion
   (b) ⇒ (a) applied to `K/N`, `(K/N) ⋊_φ̄ Z` is LEF. By `lef-implies-operator-mf` it is operator MF.
5. **Case `k ∉ N`.** Take `J = J_1`. This is the first alternative.
6. **Case `k ∈ N` and `N ≠ K`.** Take `J = J_1`. For `u, u' ∈ N_F`, eventually `U_i(u), U_i(u') ∈ A_i`. `A_i`
   is abelian, so `U_i([u,u']) = 1` exactly for large `i ∈ J_1`. Hence `π_J(N)` is abelian. This is the second
   alternative.
7. **Case `N = K`.**
   - Every `s` lies in `N_F`, so `M_i = A_i` is abelian for large `i ∈ J_1`. Hence `π_(J_1)(K)` is an abelian
     quotient of `K`. By F4 it is finite.
   - Put `N' = K ∩ ker π_(J_1)`. It is `φ`-invariant, because `π(φ(k')) = π(t) π(k') π(t)^-1`. It does not
     contain `k`, by step 1. `K/N'` is finite.
   - `(K/N') ⋊ Z` is finite-by-`Z`, hence residually finite, hence LEF, hence operator MF.
   - Take `J = J_1` and replace `N` by `N'`. This is the first alternative. ∎

## Proof of Theorem C

Suppose `π(k) ≠ 1` for some `k ∈ K`. Apply B4.
- In the first alternative, `k ∉ N`, so `N ≠ K`.
- In the second alternative, `N ≠ K` by definition.

Either way `(K/N) ⋊ Z` is a LEF quotient with `N ≠ K`, contradicting (NSL+). So `π|_K` is trivial.

**(NSL+) holds when `Rad_MF(G) = K`.** Suppose `(K/N) ⋊ Z` is LEF with `N ≠ K`. It is operator MF by
`lef-implies-operator-mf`. The quotient map `G -> (K/N) ⋊ Z` has kernel `N`. So `Rad_MF(G) ⊆ N ⊊ K`. ∎

## The (S1) reformulation

**⇐.** Let `ρ_i` be representations of `G_Γ` as stated. Then `π(s) = [ρ_i(s)]` and `π(t) = [ρ_i(t)]`. Every
relator of `G` tends to `1`, so this is a covariant model. Its lifts are exact models, since `ρ_i` kills
`R_Γ`, and they have infinite images.

**⇒.** Let `π` have exact lifts and `π(k) ≠ 1`.
- Split the index set into the finite-image stages and the infinite-image stages. For a witness, the
  compression to the finite-image stages is trivial on `K`, by Theorem C. So `‖U_i(x_k) - 1‖` stays bounded away
  from `0` along infinitely many infinite-image stages.
- Along those stages, Corollary A gives representations `(U♭_i, V_i)` of `G_Γ` with the required properties.
  The norms on `K` are unchanged, by A6.

## Scope

- The choice of `R_0` is free. It can be any finite set of relators of `K` with `<S | R_0>` Kazhdan. So a model
  is covered as soon as, for some such `R_0'`, its lifts are exact on `R_0' ∪ ŵ(R_0') ∪ {r_s}`. The constant `κ`
  then refers to `<S | R_0'>`.
- No finiteness of `M_i` is used before Theorem B.
- The only step in Theorem B that uses finiteness is F3, step 2 (the minimum distance `μ`). This is exactly
  where the infinite-image survivor (S1) escapes.
