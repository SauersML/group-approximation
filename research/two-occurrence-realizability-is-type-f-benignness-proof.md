---
rg: 2
id: two-occurrence-realizability-is-type-f-benignness-proof
kind: route
title: "Proof: the coset action straightens phi into a homomorphism, a graph embedding into H x F makes it injective, and goodness of the halting subgroup in the Boone tower is a type F benign witness"
target: two-occurrence-realizability-is-type-f-benignness
requires:
  - two-occurrence-pattern-reductions-are-power-closed
  - boone-final-group-is-of-type-f
  - boone-hnn-tower-embeds-base-group
  - boone-tower-good-subgroup-transport
  - boone-halting-subgroup-is-normal-closure
  - boone-halting-lift-is-free-on-t-and-stable-letters
  - some-type-f-group-has-re-complete-word-problem
---

Verification tier: proposed-established. These are elementary paper proofs on
top of the machine-checked Aanderaa--Cohen--Boone chain.

**Finiteness facts used.** Let `m ∈ {2, ..., ∞}` or `m = F`.

- (P) A direct product of two groups of type `F_m` is of type `F_m`.
- (A) An amalgam or HNN extension of groups of type `F_m` over subgroups of
  type `F_m` is of type `F_m`. Glue finite complexes along mapping cylinders.
  Asphericity comes from Whitehead's theorem on graphs of aspherical spaces with
  injective edge maps.
- (E) An extension of a group of type `F_m` by a group of type `F_m` is of type
  `F_m`.

## Step 1. (i) => (ii): the coset action straightens phi

Let `v =_G 1 <=> phi(v) ∈ S`. By Step 3 of
`two-occurrence-pattern-reductions-are-power-closed-proof`, the coset `S phi(v)`
depends only on the element of `G` that `v` represents, and
`S phi(v) · phi(a) = S phi(va)` for every letter `a`.

- **Inverse letters.** Let `a ∈ A`. Since `v a^-1 a =_G v`, we get
  `S phi(v a^-1) phi(a) = S phi(v a^-1 a) = S phi(v)`. Hence
  `S phi(v a^-1) = S phi(v) phi(a)^-1`.
- **The homomorphism.** Define `f : F -> H` by `f(a) = phi(a)` for `a ∈ A`.
- **Induction on `v`.** We show `S f(v) = S phi(v)` for every word `v` over
  `A ∪ A^-1`. Here `f(v)` reads a formal `a^-1` as `f(a)^-1`.
  - The empty word is clear.
  - `S f(va) = S f(v) phi(a) = S phi(v) phi(a) = S phi(va)`.
  - `S f(v a^-1) = S f(v) phi(a)^-1 = S phi(v) phi(a)^-1 = S phi(v a^-1)`.
- **Conclusion.** `f(v) ∈ S` iff `phi(v) ∈ S` iff `v =_G 1`. So `f^{-1}(S) = N`. ∎

## Step 2. (ii) => (iii) => (i), and (ii) <=> (iv)

- **(ii) => (iii).** Let `f : F -> H` be a homomorphism with `f^{-1}(S) = N`.
  - Put `Λ = H × F` and `Σ = S × F`. Both are of type `F_m` by (P), since `F` is free of finite rank.
  - Embed `F` in `Λ` by `w -> (f(w), w)`. This is injective in the second coordinate.
  - `(f(w), w) ∈ Σ` iff `f(w) ∈ S` iff `w ∈ N`. So `Σ ∩ F = N`.
- **(iii) => (i).** Take `H = Λ`, `S = Σ` and `phi` the inclusion.
- **(ii) => (iv).** Put `D = f(F)`.
  - `D ∩ S = f(f^{-1}(S)) = f(N)` is normal in `D`.
  - `ker f ⊆ f^{-1}(1) ⊆ N`, so `D/(D ∩ S) ≅ F/N = G`.
- **(iv) => (ii).** Choose `d_a ∈ D` mapping to `a ∈ G` and put `D' = <d_a>`.
  - `D' ∩ S = D' ∩ (D ∩ S)` is normal in `D'`.
  - `D'/(D' ∩ S) ≅ D'(D∩S)/(D∩S) = D/(D∩S)`, since the `d_a` generate `D` modulo `D ∩ S`.
  - Put `f(a) = d_a`. Then `f(w) ∈ S` iff the image of `w` in `D/(D∩S) ≅ G` is trivial, iff `w ∈ N`.
- **The two-occurrence reduction.** Put `K = H *_S (S × <q>)`.
  - `K` is of type `F_m` by (P) and (A).
  - By Step 4 of `two-occurrence-pattern-reductions-are-power-closed-proof`, `C_K(q) = S × <q>` and `C_K(q) ∩ H = S`.
  - So `v =_G 1` iff `[f(v), q] = 1` in `K`. The word `f(v)` has length linear in `|v|`. ∎

## Step 3. Item 2: the literal question

`G_M` is of type `F` (`boone-final-group-is-of-type-f`), and its word problem is
r.e.-complete (`some-type-f-group-has-re-complete-word-problem`). Take
`H = G_M`, `S = 1` (type `F`) and `phi` the identity on generators. Then
`phi(v) ∈ S` iff `v = 1`. ∎

## Step 4. Item 3: closure properties and the universal group

Let `N ≤ K` be `F_m`-benign with witness `(Λ, Σ)`.

- **Preimages.** Let `h : K' -> K` be a homomorphism with `K'` of type `F_m`,
  for example a free group of finite rank.
  - Embed `K'` in `Λ × K'` by `k -> (h(k), k)` and put `Σ' = Σ × K'`. Both groups are of type `F_m` by (P).
  - `(h(k), k) ∈ Σ'` iff `h(k) ∈ Σ ∩ K = N`.
  - So `h^{-1}(N)` is `F_m`-benign in `K'`.
- **Intersections.** Let `N_1` and `N_2` be `F_m`-benign in `K` with witnesses `(Λ_i, Σ_i)`.
  - Embed `K` diagonally in `Λ_1 × Λ_2`.
  - `(k, k) ∈ Σ_1 × Σ_2` iff `k ∈ N_1 ∩ N_2`.
- **Injective images.** Let `K ≤ K'` with `K'` of type `F_m`.
  - Put `Λ' = Λ *_K K'`. It is of type `F_m` by (A).
  - In the amalgam `Σ ∩ K' ⊆ Λ ∩ K' = K`, so `Σ ∩ K' = Σ ∩ K = N`.
- **The universal group.** Higman's universal group `U = F(B)/N_U` is finitely
  presented and contains a copy of every finitely generated recursively
  presented group `G = F(A)/N`.
  - Let `h : F(A) -> F(B)` lift the inclusion `G ≤ U`. Then `N = h^{-1}(N_U)`.
  - So if `N_U` is `F_m`-benign, so is every such `N` (Preimages), and item 1 gives the triple.
  - Conversely `U` is itself finitely generated and recursively presented. ∎

## Step 5. Item 4: the sandwich

- **Embedding gives a triple.** Let `ι : G -> Q` be injective with `Q` of type `F_m`. Put `f = ι ∘ π : F -> Q` with `S = 1`. Then `f^{-1}(1) = N`.
- **A triple gives a reduction.** This is Step 2.
- **Finite groups.** If `G` is finite, then `N` has finite index in `F` and is free of finite rank. `(F, N)` is a type `F` witness.
- **Quotients of type F groups by type F normal subgroups.** Let `G ≤ Γ/M` with `Γ` and `M ⊴ Γ` of type `F`.
  - The fibre product `P = {(g, h) : gM = hM} ≤ Γ × Γ` is `(M × 1) ⋊ Δ(Γ)`, an extension of `M` by `Γ`. So it is of type `F` by (E).
  - Let `γ_a ∈ Γ` lift the generator `a` of `G`, and put `f(a) = (γ_a, 1)`.
  - `f(w) ∈ P` iff `γ_w ∈ M` iff `w =_G 1`.
  - For example `Γ = Z` and `M = 2Z` give `Z/2`.
- **Torsion.** Groups of type `F` are torsion-free, so none of these groups with torsion embeds in a group of type `F`.
- **Centralizers.** An opposite-sign two-occurrence reduction `P X Q X^-1 R` into `K` normalizes, by Step 1 of the previous route, to `X ∈ C_K(Q)`. Step 1 above, with `S = C_K(Q)`, then gives `f^{-1}(C_K(Q)) = N`. ∎

## Step 6. Item 5: the type F Higman key lemma

Let `B = <t, x, y | xy = yx>`, with `t(s) = x^{-a} y^{-b} t y^b x^a` for
`s = (a, b)`, and let `G'_M` be the tower with stable letters `r_1, ..., r_n`.

- **`Λ = G'_M` is of type `F`.** It is a multiple HNN extension of
  `B ≅ Z * Z^2`, which has the finite aspherical complex `S^1 ∨ T^2`, along
  subgroups isomorphic to `B` (`boone-final-group-is-of-type-f`, whose proof
  treats `G'_M` first). So (A) applies. `B` embeds in `G'_M`
  (`boone-hnn-tower-embeds-base-group`).
- **`Σ = <t, r_1, ..., r_n>` is free of rank `n + 1`**
  (`boone-halting-lift-is-free-on-t-and-stable-letters`), so it is of type `F`.
- **`Σ = T'_M`, the subgroup generated by `T_M` and the stable letters.**
  - `(0,0) ∈ Hal`, so `t = t(0,0) ∈ T_M`. Hence `Σ ⊆ T'_M`.
  - For every `s ∈ Hal`, `t(s) = w_s^{-1} t w_s` with `w_s` a word in the stable letters, read along the halting computation (item 2 of the free-basis claim). Hence `T'_M ⊆ Σ`.
  - Both are also `<<t>>` (`boone-halting-subgroup-is-normal-closure`).
- **Goodness.** `T'_M ∩ B = T_M` (`boone-tower-good-subgroup-transport`, machine-checked). So `Σ ∩ B = T_M`.
- **Representation of r.e. sets.** For the universal machine of
  `some-type-f-group-has-re-complete-word-problem`, an r.e. set `L ⊆ N`
  satisfies `n ∈ L` iff `f(g(n)) ∈ Hal`, with `f` and `g` computable. So
  `n ∈ L` iff `t(f(g(n))) ∈ Σ`.
- **Composition.** The final sentence of item 5 is Step 4 (Preimages) with `K = B`. ∎

## Step 7. Why the join is the open step

- **Higman's route.** Higman's proof that r.e. subgroups of `F` are benign
  shows that benign subgroups are closed under a list of operations. The list
  includes joins `<N_1, N_2>` and images under non-injective maps. Every
  operation above except these has a type `F` proof: preimages, intersections
  and injective images (Step 4). The halting subgroup base case is Step 6.
- **The classical join witness.** It is `<Σ_1, Σ_2> ≤ Λ_1 *_K Λ_2`. It is
  finitely generated. Its structure as a graph of groups involves `N_1`, `N_2`
  and `N_1 ∩ N_2`, which are typically infinitely generated. We know no
  argument that makes it of type `F_3`, let alone `F`. This is the precise
  missing lemma.
- **What would suffice.** A type `F` join or normal-closure lemma, together with
  Steps 4 and 6, would prove
  `every-re-normal-subgroup-of-a-free-group-is-type-f-benign` (the benign half
  of Higman's theorem in type `F`).
- **Why the embedding half is not a barrier.** The embedding half (the rope
  trick from a benign `N` to `F/N ≤` finitely presented) is where
  `higman-rope-trick-group-is-never-fp3` bites. It is not used here, and item 4
  shows that type `F` benignness is strictly weaker than type `F` embeddability.
