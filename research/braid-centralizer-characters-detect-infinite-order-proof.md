---
rg: 2
id: braid-centralizer-characters-detect-infinite-order-proof
kind: route
title: Transfer, Nielsen–Thurston reduction and linking numbers give a centralizer character detecting each infinite-order braid
target: braid-centralizer-characters-detect-infinite-order
requires: []
artifacts:
  - research/artifacts/braid-centralizer-characters-2026-09-16.md
---

The full proof, with worked examples, is §§1–5 of the artifact. This route
records the inputs and the argument.

**Standard inputs, not re-proved.** Sources: Farb–Margalit, *A Primer on Mapping
Class Groups*, Chapters 3, 9 and 13; Ivanov, *Subgroups of Teichmüller Modular
Groups* (1992); Birman–Lubotzky–McCarthy, Duke Math. J. 50 (1983); McCarthy,
preprint (1982). None was fetched in this pass.

*Referee pins (2026-09-16), through a secondary source.* Chen–Salter,
arXiv:1804.11235v1, §2 (ar5iv HTML, read 2026-09-16) states, with these
references:
- (N1) "there exists n such that f^n fixes each element in CRS(f) and after
  cutting out CRS(f), the restriction of f^n on each component is either
  identity or pseudo-Anosov", citing Farb–Margalit Corollary 13.3. Their
  Proposition 2.2 gives `CRS(h^n) = CRS(h)`. A further power fixes every marked
  point and component. Naturality `C(hfh⁻¹) = h·C(f)` is immediate from the
  definition of `C(f)` as the intersection of all maximal reduction systems.
- (N3) is their Proposition 2.6, citing McCarthy [McC82] Theorem 1.
- (N2) is Farb–Margalit Proposition 3.20, the kernel of the cutting homomorphism.
  This number is taken from the committed artifact
  `research/artifacts/bh-birman-genus3-section-2026-09-12.md` and was not
  re-checked against the book.

In the list below, `S = S_{0,n+1}` is obtained from `D_n` by collapsing `∂D_n`
to `p_∞`. For a curve `c`, `S_c ⊆ [n]` is the set of indices of the marked points
inside `c` in `D_n`, and `χ_A({i,j}) = 1` iff `{i,j} ⊆ A`.
- **(B1) Capping.** There is a homomorphism `π : B_n → Mod(S)` with kernel
  `⟨Δ²⟩` and `π(T̃_c) = T_c`. `π(β)` fixes every `p_i` iff `β ∈ P_n`.
- **(B2) Linking numbers.** `lk_{ij} : P_n → P_2 ≅ Z` (forgetting strands) has
  `lk_{ij}(T̃_c) = χ_{S_c}({i,j})` and `lk_{ij}(Δ²) = 1`. This was checked
  numerically in `experiments/braid-centralizer-characters-2026-09-16/`.
- **(N1) Canonical reduction systems.** `C(hfh⁻¹) = h·C(f)`. Every `f` has a
  power `f^k` that, with `C = C(f^k)`:
  - fixes every marked point, every curve of `C` and every component of `S − ∪C`;
  - restricts to each component `R̂` as the identity or a pseudo-Anosov.
- **(N2) Cutting.** On `Stab⁰(C)` (classes fixing every marked point, every curve
  of `C` and every component) there are restriction homomorphisms `ρ_R`, and
  `⋂_R ker ρ_R = ⟨T_c : c ∈ C⟩`.
- **(N3) McCarthy.** The centralizer of a pseudo-Anosov is virtually infinite
  cyclic.

**Lemma T (transfer).** Let `H ≤ Z_G(g)` have finite index `j`, let
`ψ : H → Q` be a homomorphism, and suppose `ψ(g^N) ≠ 0` with `g^N ∈ H`. Then
`Φ = ψ ∘ V` is a character of `Z_G(g)` with `Φ(g) ≠ 0`, where `V` is the transfer.
- For `z` central in `Z_G(g)`, `V(z) = [z^j]`: along each cycle of `z` on the
  cosets, the transfer factors multiply to `z^ℓ`.
- So `Φ(g) = ψ(g^j)`, and `N ψ(g^j) = j ψ(g^N) ≠ 0`.

**Lemma L (laminar independence).** For a laminar family `F` of distinct subsets
of `[n]`, each of size at least 2, the vectors `χ_A` are linearly independent.
- Give each `A` a private pair `p_A ⊆ A` that lies in no child of `A`.
- Then `p_A ⊆ B` iff `A ⊆ B`, so the matrix `(χ_B(p_A))` is a unitriangular
  zeta matrix.

**Proof of the claim.** Let `n ≥ 3` (for `n ≤ 2`, `B_n` is abelian). Let `β` have
infinite order and put `f = π(β)`.
1. **Power and finite-index subgroup.** Choose `k` and `C = C(f^k)` by (N1), and
   put `g = β^k ∈ P_n`.
   - Every `h ∈ Z(β)` commutes with `g`, so `π(h)` preserves `C` by naturality.
   - Hence `H := Z(β) ∩ π⁻¹(Stab⁰(C))` has finite index in `Z(β)`, with
     `H ≤ P_n` and `g ∈ H`.
2. **Case A: some `ρ_R(f^k) = φ` is pseudo-Anosov.**
   - `θ = ρ_R ∘ π` maps `H` into `Z(φ)`, which is virtually `Z` by (N3). So
     `θ(H) ⊇ ⟨t⟩` with finite index, and `φ^a = t^b` with `a ≥ 1`, `b ≠ 0`.
   - On `H' = θ⁻¹(⟨t⟩)`, `ψ(h) := log_t θ(h)` satisfies `ψ(g^a) = b ≠ 0`.
   - Apply Lemma T with `N = ka`.
3. **Case B: every `ρ_R(f^k) = 1`.**
   - By (N2) and (B1), `g = Δ^{2e} ∏_{c∈C} T̃_c^{e_c}`, so by (B2)
     `(lk_{ij}(g))_{i<j} = e χ_{[n]} + Σ e_c χ_{S_c}`.
   - **The family.** `F = {S_c} ∪ {[n]}` is laminar, each member has size at
     least 2, and `c ↦ S_c` is injective with `S_c ≠ [n]`.
     - Sizes: `c` is essential in `S`, so `2 ≤ |S_c| ≤ n − 1`.
     - Laminar: the disks bounded by disjoint curves are nested or disjoint.
     - Injective: equal puncture sets with nested disks leave a puncture-free
       annulus, so the curves would be isotopic.
   - If all `lk_{ij}(g) = 0`, Lemma L gives `e = e_c = 0`, so `g = 1`,
     contradicting the infinite order of `β`.
   - So some `lk_{ij}(g) ≠ 0`. Apply Lemma T to `ψ = lk_{ij}|_H` with `N = k`.

In both cases `β` has infinite order in `H_1(Z_{B_n}(β); Z)`. ∎

**Related groups.** The extension to `P_n / Z(P_n) ≅ PMod(S_{0,n+1})`,
`B_n/Z(B_n)` and `Mod(S_{0,n+1})` is Lemma P and §5 of the artifact.
- (Z) passes to subgroups: restrict the character.
- (Z) passes to products: compose with a projection.
- (Z) passes to finite-index overgroups: use Lemma T on a power `g^a ∈ K`, then
  restrict from `Z_G(g^a)` to `Z_G(g)`.
- For the sphere groups, use `P_n = ker(lk_{12}) × ⟨Δ²⟩` with
  `ker(lk_{12}) ≅ PMod(S_{0,n+1})`.
