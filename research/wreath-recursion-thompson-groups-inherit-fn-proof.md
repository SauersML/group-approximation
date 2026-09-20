---
rg: 2
id: wreath-recursion-thompson-groups-inherit-fn-proof
kind: route
title: Model V_{d,r}(B, psi) by the classifying space of the cloning EI-category, attach objects by collage pushouts, and bound the descending links as polyhedral joins over d-matching complexes with fibers built from BK_1
target: wreath-recursion-thompson-groups-inherit-fn
requires: []
---

Lane proof `bh-free-06` (2026-09-18), not independently reviewed. Notation is that of the claim:
`ψ(b) = (b|_x)_x π_b`, `K_j`, `J = ∪K_j`, `K = ker(B → G)`.

## 1. The cloning category

Let `Φ = X × B` be the covering biset of `ψ`:
- the right action is `(x, c)·b = (x, cb)`;
- the left action is `b·(x, c) = (π_b(x), b|_x c)`, which is an action because `ψ` is a
  homomorphism.

**Objects and morphisms.**
- The object `n` is the free right `B`-set `R_n = [n] × B`.
- Splitting strand `i` along a finite tree replaces `{i} × B ≅ B` by `⊔_{leaves v} {v} × B`, which
  is iterated `B ⊗_B Φ` along the tree.
- For a forest `F` with `n` roots and `m` leaves this produces `R_F`, and ordering the leaves gives
  a canonical isomorphism `R_F ≅ R_m`.
- A morphism `n → m` is a pair `(F, θ)` with `θ : R_F → R_m` an isomorphism of right `B`-sets.
  Via the canonical identification, `θ` is an element `α ∈ Aut(R_m) = B ≀ S_m`, so morphisms are
  pairs `(F, α)`.

**Composition.**
- An isomorphism of free right `B`-sets maps strands to strands by left multiplications `λ_b`.
- `λ_b` transports a tree `T` on the target strand to the tree `b^{−1}(T)` on the source strand,
  and it induces `(v, c) ↦ (b(v), b|_v c)` on leaves.
- So `(F', α') ∘ (F, α) = (α^*F' ∘ F, α' ∘ α_*)`.
- Associativity is functoriality of `− ⊗_B Φ`. This is the Zappa–Szép product of forests with
  `⊔_n B ≀ S_n`; for injective `ψ` it is Skipper–Zaremsky's cloning category `S_* ≀ G`.

**Basic facts.**
- **(EI)** Morphisms `n → m` exist only when `m ≥ n` and `m ≡ n mod (d−1)`. `End(n) = Aut(n)
  = Γ_n := B ≀ S_n`.
- **(Left cancellation)** If `f ∘ s = g ∘ s`, then `f = g`. Indeed, `s^*` is a bijection on
  forests and `s_*` is an isomorphism.
- **(Precomposition stabilizers)** Let `f = (F, α) : c → m` and `a = (σ; a_1, ..., a_c) ∈ Γ_c`.
  - `f ∘ a = f` if and only if `σ = 1`, `a_i ∈ K_{T_i}` for the tree `T_i` of `F` at root `i`,
    and `a_i = 1` at trivial trees.
  - Here `K_T` is the set of elements fixing the leaves of `T` with trivial sections there. So
    `K_{caret} = K_1`.

## 2. Localization and identification

**Lemma 1.** `𝒞` admits a calculus of left fractions, and the localization functor
`L : 𝒞 → 𝒢 = 𝒞[𝒞^{−1}]` induces a homotopy equivalence `B𝒞 ≃ B𝒢`.

*Proof.*
- **Ore condition.** Let `f = (F, α) : a → b` and `g = (F', α') : a → c`.
  - Pick a common refinement `E` of `F` and `F'`.
  - Let `u = ((α^*)^{−1}(E∖F), 1)`, so that `u ∘ f = (E, β)`. Likewise `v ∘ g = (E, β')`.
  - Replace `u` by `(β' β^{−1}) ∘ u`. Then `u ∘ f = v ∘ g`.
- **Cancellation axiom.** "If `f ∘ s = g ∘ s` then `t ∘ f = t ∘ g` for some `t`" holds with
  `t = id`, by left cancellation.
- So Gabriel–Zisman's calculus of left fractions applies (standard; not re-read):
  - (i) every morphism of `𝒢` is `L(s)^{−1} L(f)`;
  - (ii) `L(f) = L(g)` if and only if `t ∘ f = t ∘ g` for some `t`.
- **Filteredness.** For an object `y` of `𝒢`, consider the comma category `y/L`.
  - Two objects `(c, φ)` and `(c', φ')` map to a common one by (i), applied to `φ' φ^{−1}`.
  - Parallel arrows `f, g` satisfy `L(f) = L(g)`, so by (ii) some `t` coequalizes them.
  - So `y/L` is filtered, hence contractible (Quillen). Quillen's Theorem A gives the claim. `∎`

`𝒢` has components `r = 1, ..., d−1`. Write `V_{d,r}(B, ψ) := Aut_𝒢(r)`. Then `B𝒢 = ⊔_r
BV_{d,r}(B, ψ)`.

**Lemma 2 (identification).** Let `𝒱` be the Röver–Nekrashevych groupoid of `G`: its morphisms
`C(n) → C(m)` are piecewise prefix replacements followed by elements of `G`, where `C(n) = [n] ×
X^ω`. Let `Λ(F, α) = ᾱ ∘ x_F`. Then `Λ` factors through `𝒢`, and the induced functor `𝒢 → 𝒱` is
surjective. It is injective, hence an isomorphism, if and only if `J = K`. Moreover `𝒢(B, ψ) ≅
𝒢(B/J, ψ̄)`.

*Proof.*
- **Surjectivity.** Every morphism of `𝒱` is a tree pair with `G`-labels. Lift the labels to `B`.
- **When `Λ(f) = Λ(g)`.** Let `f = (F, α)` and `g = (F', α')` be parallel.
  - The partition of `C(n)` into preimages of the target copies is the leaf partition of `F`. So
    `Λ(f) = Λ(g)` forces `F = F'` and `α' = α k` with `k ∈ K^m`.
- **When `L(f) = L(g)`.** By Lemma 1(ii) this means `t ∘ f = t ∘ g` for some `t = (T, γ)`.
  - Then `Λ(f) = Λ(g)`, since `Λ(t)` is invertible. So `F = F'` and `α' = α k`.
  - `α_*` and `(αk)_*` agree on `R_{α^*T ∘ F}` if and only if each `k_ℓ ∈ K_{T_ℓ}`.
  - Since `∪_T K_T = ∪_j K_j = J`, `L(f) = L(g)` if and only if `F = F'` and `k ∈ J^m`.
- **Conclusion.** `𝒢 → 𝒱` is injective exactly when `J^m = K^m`.
- **`B/J`.** `J` is `ψ`-saturated: `ψ(K_{j+1}) ⊆ K_j^d`. So `ψ̄` exists, and it is injective. The
  same computation, done modulo `J`, gives `𝒢(B, ψ) ≅ 𝒢(B/J, ψ̄)`. `∎`

## 3. Attaching one object

Fix a component. Let `𝒞_{≤m}` be the full subcategory on objects `≤ m`.

**Collage lemma** (standard; e.g. the homotopy type of a correspondence / cograph; not re-derived
here). Let `𝒟` be a category with a functor to `[1]` with fibers `𝒟_0, 𝒟_1`. Let `A` be the
category of arrows from `𝒟_0` to `𝒟_1`, with commuting squares as morphisms. Then `B𝒟` is the
homotopy pushout of `B𝒟_0 ← BA → B𝒟_1`.

**Applying it.**
- Take `𝒟 = 𝒞_{≤m}`, `𝒟_0 = 𝒞_{<m}` and `𝒟_1 = {m}` with `Γ_m`.
- `A` is the Grothendieck construction of `Γ_m` acting, by postcomposition, on the over-category
  `𝒪_m := 𝒞_{<m} ↓ m`. This action is **free**, since `β(F, α) = (F, βα)`.
- Put `L_m := N(𝒪_m)`. Then
  `B𝒞_{≤m} ≃ B𝒞_{<m} ∪_{(L_m)_{hΓ_m}} BΓ_m`.
- The map `(L_m)_{hΓ_m} → BΓ_m` has fiber `L_m`. So if `L_m` is `(k−1)`-connected, then
  `B𝒞_{<m} → B𝒞_{≤m}` is `k`-connected.

## 4. Stein retraction

Let `E_m ⊆ 𝒪_m` be the full subcategory of **elementary** arrows: every tree of the forest has
depth at most 1.

**Lemma 3.** `N(E_m) ↪ L_m` is a `Γ_m`-equivariant homotopy equivalence.

*Proof.*
- For `f = (F, α)`, let `E_F` be the bottom carets of `F`, so that `F = E_F ∘ F'`.
- Put `e(f) = (E_F, α)` and `h_f = (F', 1)`. Then `e(f) ∘ h_f = f`, and `e(f) ∈ E_m`, because a
  non-identity forest has a bottom caret.
- **Functoriality.** For `g : f_1 → f_2` there is a unique `u` with `u ∘ h_{f_1} = h_{f_2} ∘ g`.
  - It exists because the bottom carets of `f_2` are, after transport, bottom carets of `f_1`.
  - It is unique because precomposition with a pure forest is injective (§1).
  - Uniqueness gives functoriality of `r(g) := u`, and `e(f_2) ∘ u = e(f_1)`.
- So `r` is a functor `𝒪_m → E_m`, and `h` is a natural transformation `id ⇒ i ∘ r`. Moreover
  `r ∘ i = id`. Both commute with postcomposition. `∎`

## 5. The elementary descending link is a polyhedral join

Let `M_m` be the simplicial complex whose simplices are the families of pairwise disjoint
`d`-subsets of `[m]`.

For a `d`-subset `I` of `[m]`:
- let `Ω_I` be the set of pairs `(ε, (g_x)_{x∈X})`, with `ε : X → I` a bijection and `g_x ∈ B`;
- `B` acts on `Ω_I` on the right through `ψ`, with stabilizers conjugate to `K_1`;
- let `𝒟_I` be the action groupoid, and put `Y_I := B𝒟_I ≃ ⊔_{Ω_I/ψ(B)} BK_1`. It is nonempty.

**Lemma 4.** `N(E_m) ≃ ∗_{M_m} Y_I`, the polyhedral join `∪_{σ ∈ M_m} ∗_{I∈σ} Y_I`.

*Proof.*
- **Invariants of an object.** An elementary `f = (F, α)` determines:
  - the matching `M(f)`, the images under `α` of the leaf sets of the carets;
  - for each block `I ∈ M(f)`, a decoration in `Ω_I/ψ(B)`, namely `α` restricted to that caret's
    leaves.
- **Objects and automorphisms.** By §1, these data are exactly the isomorphism invariant of `f` in
  `E_m`, and `Aut(f) = ∏_{I ∈ M(f)} K_1`. The labels on unmerged leaves are absorbed by
  precomposition.
- **Morphisms.** `Hom(f', f)` is nonempty if and only if `M(f) ⊆ M(f')` and the decorations agree
  on `M(f)`.
  - It is then an `Aut(f)`-torsor: the free parameters are the `K_1`-ambiguities of the labels at
    the carets of `f`.
  - `Aut(f')` acts through the projection `∏_{M(f')} K_1 → ∏_{M(f)} K_1`.
- **Grothendieck construction.** Let `P` be the poset of decorated matchings. Choose one
  representative per element of `P`, with fixed decoration representatives and trivial labels
  elsewhere. Then `E_m` is equivalent to the Grothendieck construction of `P ∋ (M, δ) ↦
  ∏_{I∈M}(∗//K_1)`, with projections as the transition functors.
- **Thomason.** By Thomason's theorem, `N(E_m) ≃ hocolim_P ∏_{I∈M} BK_1`.
  - A hocolim over the face poset of a complex, of products of fibers with projections to faces,
    is the polyhedral join. Grouping decorations by block gives the fibers `Y_I` over `M_m`. `∎`

For `ψ` injective, `K_1 = 1` and `Y_I` is discrete. This is the classical decorated matching
descending link.

## 6. Connectivity

**Lemma 5 (polyhedral joins).** Let `L` be a finite complex that is weakly Cohen–Macaulay of
dimension `n`: it is `(n−1)`-connected, and `lk(σ)` is `(n−p−2)`-connected for every `p`-simplex
`σ`. Let `(Y_v)` be nonempty CW complexes. Then `∗_L Y_v` is `(n−1)`-connected.

*Proof.* Induction on `n`. The case `n = 0` holds since `L ≠ ∅`.

For `n ≥ 1`, replace the `Y_v` by their cones `CY_v`, one vertex at a time. Suppose the current
fibers are `Y'_u ∈ {Y_u, CY_u}`, and let `W = ∗_{lk(v)} Y'_u`.
- **The step is a pushout.** The step at `v` is the pushout of `Z_old ⊇ Y_v * W ⊆ CY_v * W`.
- **Connectivity of `W`.** `lk(v)` is wCM of dimension `n − 1` and nonempty, since `n ≥ 1`. So by
  induction `W` is `(n−2)`-connected.
- **Connectivity of the join.** `Y_v * W` is `(−1 + (n−2) + 2) = (n−1)`-connected, and
  `CY_v * W` is contractible. So the pair is `n`-connected, and `π_i(Z_old) ≅ π_i(Z_new)` for
  `i ≤ n−1`.
- **End of the process.** `∗_L CY_v ≃ ∗_L(pt) = L` by homotopy invariance, and `L` is
  `(n−1)`-connected. `∎`

**Lemma 6 (grounding).** `M_m` is wCM of dimension `ν(m) = ⌊(⌊m/d⌋ − 1)/d⌋`.

*Proof.*
- **Grounding.** A matching with `⌊m/d⌋` blocks is a `(⌊m/d⌋−1)`-simplex. Every `d`-set meets at
  most `d` of its blocks, so it is a `d`-ground in the sense of Belk–Matucci arXiv:1312.2282,
  Def. 6.1.
- **Connectivity.** Faces of a ground are grounds. By Belk–Forrest, as stated in Belk–Matucci
  Thm 6.2 ("every finite `(mk,k)`-grounded flag complex is `(m−1)`-connected"), `M_m` is
  `(ν(m)−1)`-connected. `M_m` is flag.
- **Links.** The link of a `p`-simplex is `M_{m−d(p+1)}`, and `ν(m − d(p+1)) ≥ ν(m) − (p+1)`.
  So the links have the required connectivity. `∎`

**Consequence.** By Lemmas 3–6, `L_m` is `(ν(m)−1)`-connected for every `B` and `ψ`. So
`B𝒞_{<m} → B𝒞_{≤m}` is `ν(m)`-connected, and `ν` is nondecreasing and unbounded.

## 7. Finiteness and conclusion

**Lemma 7.** If `B` has type `F_n`, then every `B𝒞_{≤m}` has the homotopy type of a CW complex
with finite `n`-skeleton.

*Proof.* Induction on `m` through §3.
- **The base.** `BΓ_m` has finite `n`-type, because `Γ_m = B ≀ S_m` has type `F_n`.
- **The attaching space.** By Lemmas 3 and 4, `(L_m)_{hΓ_m}` is a homotopy colimit over the
  finite EI-category `P//Γ_m`. Its values are `(∏_{I∈M} BK_1)_{h Stab(M,δ)}`.
  - `Stab(M, δ)` is `B^{unmerged}` times `∏_I Stab_{Γ_I}(δ_I)` times a finite permutation part,
    where `Γ_I = B ≀ Sym(I)` acts simply transitively on `Ω_I`.
  - `Stab_{Γ_I}(δ_I) ≅ ψ(B) ≅ B/K_1`. So `(BK_1)_{h(B/K_1)} ≃ BB`.
  - Each value is therefore `B` of a group `B^a ⋊ (finite)`, which has type `F_n`.
  - A homotopy colimit over a finite EI-category with such values, and with morphism sets
    finite modulo automorphisms, has finite `n`-type, by the same collage induction.
- **Pushouts.** Homotopy pushouts preserve finite `n`-type. `∎`

**Lemma 7, the stabilizers written out** (bh-sz-vdg, 2026-09-19, as the referee bh-ref-q12 asked). This
replaces the phrase "morphism sets finite modulo automorphisms" above.

**The category.** Let `𝒢_m = E_m ⋊ Γ_m` be the Grothendieck construction of `Γ_m` acting on `E_m` by
postcomposition.
- Objects are the elementary arrows `f = (F, α) : c → m` with `c < m`.
- A morphism `f_1 → f_2` is a pair `(β, g)` with `β ∈ Γ_m` and `g : c_1 → c_2` in `𝒞`, such that
  `f_2 ∘ g = β ∘ f_1`.
- By Thomason's theorem and Lemma 3, `(L_m)_{hΓ_m} ≃ B𝒢_m`.
- `𝒢_m` is EI: an endomorphism has `g ∈ End(c) = Γ_c`.

(a) **Objects.** The isomorphism class of `f` is determined by the number `k` of carets of `F`, with
`1 ≤ k ≤ ⌊m/d⌋`. The reason is that `S_m ⊆ Γ_m` acts transitively on the `k`-block matchings, and `Γ_I` acts
simply transitively on `Ω_I`, so on decorations too. So there are finitely many isomorphism classes.

(b) **Automorphisms.** The map `(β, g) ↦ g` is an isomorphism from `Aut_{𝒢_m}(f)` onto
`Stab_{Γ_c}(F) = {g = (σ; g_1, …, g_c) : σ preserves the caret roots of F} ≅ (B ≀ S_k) × (B ≀ S_{c−k})`.
- For `g ∈ Γ_c` we have `f ∘ g = (g^*F, α g_*)` and `β ∘ f = (F, βα)`.
- These are equal iff `g^*F = F` and `β = α g_* α^{−1}`.
- `g^*F = F` means exactly that `σ` preserves the caret roots, because each `λ_b` permutes the children of a
  vertex and so carries carets to carets.
- So `β` is determined by `g`.

(c) **Morphisms.** Let `(β, g) : f_1 → f_2` with `g = (G, γ)`.
- **Shape.** `G` is elementary with `k_1 − k_2` carets, and `β^{−1}`-transported `F_1 = γ^*F_2 ∘ G`. So the roots
  `[c_1]` split into three classes:
  - roots of new carets, the carets of `G`, of size `k_1 − k_2`;
  - roots of old carets, those coming from `F_2`, of size `k_2`;
  - trivial roots, of size `c_1 − k_1`.
- **Orbits.** `Aut(f_1) × Aut(f_2)` acts on `Hom(f_1, f_2)` by `(a_1, a_2)·φ = a_2 φ a_1^{−1}`. There is one orbit
  for each combinatorial splitting. With `f_1` and `f_2` fixed, this is a choice of which `k_2` of the `k_1` carets
  are old, and `Aut(f_1) ⊇ B ≀ S_{k_1}` moves these choices transitively. So there are finitely many orbits.
- **Stabilizers.** Under (b), the stabilizer of `φ` is identified with the subgroup of `Stab_{Γ_{c_1}}(F_1)`
  preserving the three classes: `(B ≀ S_{k_1−k_2}) × (B ≀ S_{k_2}) × (B ≀ S_{c_1−k_1})`.
  - Given `a_1` in that subgroup, the `a_2` with `a_2 g = g a_1` is determined: on the leaves of `G` it is the
    action transported from `a_1`, and elsewhere it equals `a_1`.
  - This `a_2` lies in `Stab(F_2)`, because it preserves the old caret roots as a set.

(d) **Chains.** A chain of non-isomorphisms `f_0 → f_1 → ⋯ → f_j` has `k_0 > k_1 > ⋯ > k_j`. It splits the roots
of `c_0` into the trivial roots and the carets, graded by the step at which they were added. Its stabilizer in
`Aut(f_0)` is the product of `B ≀ S_{(size of class)}` over the classes, and there are finitely many chain types.

So every group appearing in the collage induction of §3 for `𝒢_m` (automorphism groups, stabilizers of morphisms,
stabilizers of chains) is a finite-index overgroup of a power of `B`, hence of type `F_n`, and there are finitely
many isomorphism types at each stage. The induction therefore gives `B𝒢_m` finite `n`-type, which is what the
attaching step of Lemma 7 uses. The earlier count `(BK_1)_{h(B/K_1)} ≃ BB` computes the same homotopy type from the
`E_m` side, as the referee noted.

**Proof of the Theorem.**
- Choose `m` with `ν(m) ≥ n`. Then `B𝒞_{≤m} → B𝒞_{[r]} ≃ BV_{d,r}(B, ψ)` is `n`-connected, by §6
  and Lemma 1.
- `B𝒞_{≤m}` has finite `n`-type by Lemma 7.
- Attaching cells of dimension `≥ n+1` produces a `K(V_{d,r}(B,ψ), 1)` with finite `n`-skeleton.
  So `V_{d,r}(B, ψ)` has type `F_n`.
- Part 2 of the claim is Lemma 2. `∎`

## 8. Consequences, with sources

All citations below are from Nekrashevych arXiv:1312.5654, TeX `thompson.tex`, read at source
2026-09-18.
1. **Contracting `G`.**
   - We may assume the nucleus `N` generates `G`, since `V_{⟨N⟩} = V_G` (text after Prop.
     `pr:lengththree`).
   - Let `B = ⟨N | g_1g_2g_3 = 1 whenever this holds in G⟩`. It is finitely presented, and its
     biset is contracting (Prop. `pr:lengththree`, l.1646).
   - Nucleus elements are nontrivial in `G`, so the kernel is `∪K_j` (Prop.
     `pr:kernelcontracting`, l.1668).
   - With `n = 2` this re-proves `th:finitepresentation` (l.1948).
2. **Expanding maps.** Let `f : M_1 → M` be expanding, with `M` compact, path-connected and
   semi-locally simply connected.
   - "If `g ∈ π_1(M)` has trivial image in `IMG(f)`, then there exists `n` such that `g` acts
     trivially from the left on `Φ_f^{⊗n}`" (Prop. `pr:expandingpi1`, l.1710). That says `K = J`.
   - `V_Φ ≅ V_f = V_{IMG(f)}` (Corollary at l.1729).
3. **Grigorchuk group.**
   - The nucleus is `{1, a, b, c, d}`: Belk–Matucci, proof of their Prop. 2.6.
   - Its products of two elements lying in `N` are `a^2 = b^2 = c^2 = d^2 = 1` and `bc = cb = d`,
     `bd = db = c`, `cd = dc = b`.
   - So `B = C_2 * (C_2 × C_2)`, which is virtually free and has type `F_∞`. Hence `V(G)` has
     type `F_∞`.

**Lesson for general BH.** See the claim. In short, labels enter the finiteness of a Thompson
envelope only through the automorphism groups `B ≀ S_m` of a category, and they need not inject.
Descending links fatten by `BK_1`, and this is harmless because the joins are taken over a
Cohen–Macaulay complex.
