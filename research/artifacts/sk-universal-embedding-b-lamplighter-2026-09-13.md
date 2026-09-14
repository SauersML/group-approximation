# Lamplighter crossed products: every f.g. LEF group lies in an infinite simple Kazhdan LEF group

Lane `sk-universal-embedding-b`, 2026-09-13. Written proof, unreviewed. Supports
`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` and the route
`lef-groups-embed-in-simple-kazhdan-lef-groups-proof`.

**Idea.** Freeness and exact periodic models force residually finite acting groups
(`free-rf-actions-force-residually-finite-groups`). Minimality has been the obstacle for partial models
(`lef-groups-embed-in-simple-kazhdan-lef-groups`, Attempts). Both disappear for the lamplighter action of
`Z/2 ≀ Δ` on `2^Δ`:
- minimality comes from flipping finitely many coordinates;
- every configuration is legal, so partial models are just configurations on a finite group;
- injectivity of the matricial map comes from simplicity, so topological freeness suffices.

## 0. Setup

- `Δ`: a finitely generated infinite group, finite generating set `S`, word balls `B_r`.
- `Z = 2^Δ = {0,1}^Δ`, a Cantor set.
- `(δ·x)(h) = x(δ^(-1)h)` for `δ ∈ Δ`.
- `(a·x)(h) = x(h) + [h = e]` mod 2, the flip at `e`.
- `L = ⟨Δ, a⟩ ≤ Homeo(Z)`.
- `R = LC(Z, F_2) ⋊ L`, with `u_ℓ f u_ℓ^(-1) = f ∘ ℓ^(-1)`.

`δaδ^(-1)` is the flip at `δ`: `(δaδ^(-1)x)(h) = (aδ^(-1)x)(δ^(-1)h) = x(h) + [h = δ]`.
So `L` consists of the affine maps `x ↦ δ·x + f`, with `δ ∈ Δ` and `f ∈ ⊕_Δ Z/2`, and `L ≅ Z/2 ≀ Δ`. It is generated
by `S ∪ {a}`.

## 1. Dynamics

**Lemma 1.** `L ↷ Z` is minimal and topologically free. `R` is generated as a ring by `u_s^(±1)` (`s ∈ S`), `u_a`, and
`p = 1_[x(e)=1]`.

*Proof.*
- **Minimality.** The orbit of `x` contains `x + ⊕_Δ Z/2`, which is dense.
- **Topological freeness.** Let `ℓ = (x ↦ δx + f) ≠ 1`.
  - If `δ = e`, then `f ≠ 0`, and `ℓ` has no fixed point.
  - If `δ ≠ e`, fix a cylinder on a finite `W ⊆ Δ`. Since `Δ` is infinite there is `h` with `h, δ^(-1)h ∉ W ∪ supp f`.
    These are two different coordinates. Take `x` in the cylinder with `x(h) ≠ x(δ^(-1)h)`.
    Then `(ℓx)(h) = x(δ^(-1)h) ≠ x(h)`. So `Fix(ℓ)` has empty interior.
- **Generation.** `u_δ p u_δ^(-1) = 1_[x(δ)=1]`. Cylinders are finite products of these and their complements. Locally
  constant functions are finite sums of cylinder indicators. Every `u_ℓ` is a product of generators. ∎

Also `x ↦ (ℓ ↦ (ℓ^(-1)x)(e))` is injective, since `(δ^(-1)x)(e) = x(δ)`. So `Z` is an `L`-subshift over `{0,1}`.

**Lemma 2.** `R` is simple and `Z(R) = F_2`.

*Proof* (the direct argument of the manuscript, l.102-113, with free points in place of freeness).
- Each `Fix(ℓ)` is closed with empty interior, and `L` is countable. By Baire the free points are dense.
- **Simplicity.** Let `I ≠ 0` be an ideal. Multiplying by some `u_ℓ`, it contains `r = Σ f_ℓ u_ℓ` with `f_1 ≠ 0`.
  - Pick a free point `x_0` with `f_1(x_0) = 1`.
  - Pick a clopen `U ∋ x_0` with `f_1|_U = 1` and `U ∩ ℓU = ∅` for the finitely many `ℓ ≠ 1` in the support of `r`.
  - Then `1_U r 1_U = 1_U`.
  - By minimality finitely many translates `ℓ_i U` cover `Z`, so `1 = 1 - Π_i (1 - 1_(ℓ_i U)) ∈ I`.
- **Centre.** Let `r = Σ f_ℓ u_ℓ` be central.
  - `[1_V, r] = Σ f_ℓ (1_V - 1_(ℓV)) u_ℓ` vanishes for every clopen `V`. So `f_ℓ(x) = 0` whenever `ℓ^(-1)x ≠ x`, which forces
    `supp f_ℓ ⊆ Fix(ℓ^(-1))`.
  - A clopen subset of a set with empty interior is empty, so `f_ℓ = 0` for `ℓ ≠ 1`.
  - Commuting with `u_s` and `u_a` makes `f_1` invariant, so `f_1` is constant by minimality. ∎

## 2. Matricial models from LEF models of Δ

Let `Δ` be LEF: there are finite groups `Q_n` and injective maps `φ_n : B_n -> Q_n` with `φ_n(gh) = φ_n(g)φ_n(h)`
whenever `g, h, gh ∈ B_n`.
- Put `E_n = 2^(Q_n) × Q_n` and `N_n = |E_n|`.
- To `z = (c, q) ∈ E_n` attach the partial configuration `x_z(h) = c(qφ_n(h))`, `h ∈ B_n`.
- Define permutations of `E_n`: `σ_s(c,q) = (c, qφ_n(s)^(-1))` for `s ∈ S`, and `σ_a(c,q) = (c + 1_q, q)`.

**Lemma 3.** Fix `r`. For `n` large and every word `w` of length `≤ r` representing `ℓ = (x ↦ δx + f)`:
`σ_w(c,q) = (c + Σ_(h ∈ supp f) 1_(q'φ_n(h)), q')`, with `q' = qφ_n(δ^(-1))`.
- In particular `σ_w` depends only on `ℓ`. Write `σ_ℓ`. Then `σ_(ℓℓ') = σ_ℓ σ_(ℓ')` for `|ℓ|, |ℓ'| ≤ r/2`.
- `x_(σ_ℓ z) = ℓ · x_z` on `B_(n/2)`.

*Proof.* Induction on the length of `w`, using the partial homomorphism and injectivity of `φ_n` on `B_n`.
- A letter `s` replaces `δ` by `sδ` and translates `supp f` by `s`.
- The letter `a` adds `1_e` to `f`.
- The displayed formula is the model of `x ↦ δx + f`:
  `x_(σ z)(h) = c(qφ_n(δ^(-1)h)) + f(h) = x_z(δ^(-1)h) + f(h)`.
- Distinct elements of `B_n` have distinct images, so the formula for `ℓ` does not depend on `w`. ∎

**Diagonal.** For `f ∈ LC(Z,F_2)` depending on coordinates in `B_ρ`, let `D_n(f)` be diagonal on `F_2^(E_n)` with entry
`f(x_z)`, evaluated on any extension of `x_z|_(B_ρ)`. Every configuration on `B_ρ` is legal in `Z`, so no window can
fail. Put `P_σ δ_z = δ_(σz)`.

**Proposition 4.** `π_n(Σ f_ℓ u_ℓ) = Σ D_n(f_ℓ) P_(σ_ℓ)` defines a unital injective ring homomorphism
`π = (π_n)_ω : R -> ∏_ω M_(N_n)(F_2)`.

*Proof.*
- `P_(σ_ℓ) D_n(f) P_(σ_ℓ)^(-1) δ_(σ_ℓ z) = f(x_z) δ_(σ_ℓ z)`.
- `(f∘ℓ^(-1))(x_(σ_ℓ z)) = f(ℓ^(-1)·ℓ·x_z) = f(x_z)` by Lemma 3.
- With `σ_(ℓℓ') = σ_ℓσ_(ℓ')`, this gives `π_n(rs) = π_n(r)π_n(s)`, `π_n(r+s) = π_n(r)+π_n(s)` and `π_n(1) = 1` for
  fixed `r, s` and all large `n`.
- So `π` is a unital ring homomorphism. Its kernel is a proper ideal of the simple ring `R` (Lemma 2), hence `0`. ∎

## 3. The groups

**Theorem 5.** Let `Δ` be finitely generated, infinite and LEF, and `n ≥ 3`. Then `G = EL_n(R)` is an infinite,
finitely generated, simple group with property (T) that is LEF. The map `ℓ ↦ diag(u_ℓ,1,…,1)` embeds
`[L,L] ⊇ [Δ,Δ]` in `G`.

*Proof.*
- **Property (T).** `R` is finitely generated (Lemma 1), so EJZ applies (`elementary-groups-over-fg-rings-have-property-t`).
- **Simplicity.** The transformation groupoid of a minimal topologically free action on the Cantor set is a minimal,
  effective, Hausdorff ample groupoid with compact infinite unit space. So every normal subgroup of `G` is central or
  all of `G` (`steinberg-elementary-groups-are-simple-mod-centre`). A central element commutes with every `e_ij(1)`, so
  it is a scalar `c·1` with `c ∈ Z(R)^× = {1}` (Lemma 2). So `G` is simple.
- **LEF.** `π` gives an injective homomorphism `GL_n(R) -> ∏_ω GL_(nN_k)(F_2)`, an algebraic ultraproduct of finite
  groups. A countable subgroup of such an ultraproduct is LEF: a finite subset and its multiplication table are
  realized in `ω`-most factors.
- **Infinite.** `e_12(LC(Z,F_2))` is infinite.
- **Embedding.** `L ↪ GL_1(R)` through `ℓ ↦ u_ℓ`. For units `a, b`, `diag(a,a^(-1)) diag(b,b^(-1)) diag((ab)^(-1), ab)
  = diag(1, a^(-1)b^(-1)ab)`. Whitehead's lemma puts each `diag(c, c^(-1))` in `E_2(R)`. So `diag(1,[x,y]) ∈ E_2(R)`;
  conjugate by `e_12(1)e_21(1)e_12(1)` to reach `diag([x,y],1)`. So `c ↦ diag(c,1,…,1)` maps
  `[GL_1(R),GL_1(R)]` homomorphically and injectively into `E_2(R) ≤ G`. ∎

**Corollary 6.** A finitely generated group is LEF if and only if it is a subgroup of an infinite, finitely generated,
simple group with property (T) that is LEF.

*Proof.*
- (⇐) Subgroups of LEF groups are LEF.
- (⇒) By `rf-groups-lie-in-derived-subgroups-of-rf-groups` (2) there is a f.g. LEF `Δ` with `Γ ≤ [Δ,Δ]`. Replacing
  `Δ` by `Δ × Z` keeps it f.g., LEF and infinite, and `[Δ×Z, Δ×Z] = [Δ,Δ] × 1` still contains `Γ`.
- Theorem 5 gives `Γ ≤ [Δ,Δ] ≤ [L,L] ↪ G`. ∎

## 4. Remarks and model tests

- `Δ = Z` gives the lamplighter `Z/2 ≀ Z` on `2^Z` and one simple Kazhdan LEF group `EL_3(LC(2^Z,F_2) ⋊ (Z/2 ≀ Z))`.
  This is a new witness for the manuscript's theorem, different from subshift crossed products.
- **Residually finite Γ.** This route replaces the Toeplitz construction of `rf-groups-embed-in-simple-kazhdan-lef-groups`
  by a shorter one.
- **Non-LEF Δ.** Lemmas 1-2 and simplicity still hold, but `G ⊇ [Δ,Δ]`, so `G` is not LEF when `[Δ,Δ]` is not. That is
  consistent.
- **Finite Δ.** `Z` is finite, and Lemma 1 fails (no Cantor set, no topological freeness). It is excluded by hypothesis.
- **Why not free.** `x ↦ δx` fixes the `δ`-periodic configurations, so the action is only topologically free. This is
  why simplicity goes through `steinberg-elementary-groups-are-simple-mod-centre` and not the tower partition, which needs
  freeness everywhere (`finite-model-subshift-elementary-groups-simple-kazhdan-lef`).
- **Novelty check (bounded).** Only a Cairn grep of main (lamplighter, wreath Bernoulli, flip), and the peer nodes cited
  above. No literature search. Kionke–Schesler Theorem 1.2 takes residually finite input and gives no (T).
