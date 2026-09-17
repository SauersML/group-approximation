import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.Extension
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ↪ R^ω`: the graph spanned by a family of generator pairs

`simple_kazhdan_sofic_group.tex`:

> (tex 345–348) … and $L(G)$ embeds in $\mathcal R^\omega$.
>
> (tex 350–355) … $L(G)\mathbin{\bar\otimes}\mathcal R$ … embeds in $\mathcal R^\omega$.

Step 4 of the route described in `ROmega/TwoNorm`.  A family `U : Λ → B(H) × N^ω` whose linear
span contains `1` and is closed under products and adjoints of generators spans a `⋆`-subalgebra,
the graph `spanGraph`.  Membership of the first coordinates in `M`, trace compatibility and density
only have to be checked on the generators, and `exists_injective_of_generators` feeds the graph to
`exists_extension`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter TracialUltrapower
open scoped InnerProductSpace Topology

noncomputable section

universe v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M)
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {N : VonNeumannAlgebra K} {σ : TracialVector N} {ω : Ultrafilter ℕ}
variable {Λ : Type*} (U : Λ → (H →L[ℂ] H) × Ultrapower σ ω)

/-- The span of a family closed under products of generators is closed under products. -/
theorem mul_mem_span (hmul : ∀ g h, U g * U h ∈ Submodule.span ℂ (Set.range U))
    {a b : (H →L[ℂ] H) × Ultrapower σ ω} (ha : a ∈ Submodule.span ℂ (Set.range U))
    (hb : b ∈ Submodule.span ℂ (Set.range U)) : a * b ∈ Submodule.span ℂ (Set.range U) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      exact hmul g h
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

/-- The span of a family closed under adjoints of generators is closed under adjoints. -/
theorem star_mem_span (hstar : ∀ g, star (U g) ∈ Submodule.span ℂ (Set.range U))
    {a : (H →L[ℂ] H) × Ultrapower σ ω} (ha : a ∈ Submodule.span ℂ (Set.range U)) :
    star a ∈ Submodule.span ℂ (Set.range U) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hstar g
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ (star c) hx

/-- **The graph spanned by the generator pairs.** -/
def spanGraph (hone : (1 : (H →L[ℂ] H) × Ultrapower σ ω) ∈ Submodule.span ℂ (Set.range U))
    (hmul : ∀ g h, U g * U h ∈ Submodule.span ℂ (Set.range U))
    (hstar : ∀ g, star (U g) ∈ Submodule.span ℂ (Set.range U)) :
    StarSubalgebra ℂ ((H →L[ℂ] H) × Ultrapower σ ω) where
  carrier := (Submodule.span ℂ (Set.range U) : Set ((H →L[ℂ] H) × Ultrapower σ ω))
  mul_mem' := fun ha hb ↦ mul_mem_span U hmul ha hb
  one_mem' := hone
  add_mem' := fun ha hb ↦ Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c hone
  star_mem' := fun ha ↦ star_mem_span U hstar ha

variable (hone : (1 : (H →L[ℂ] H) × Ultrapower σ ω) ∈ Submodule.span ℂ (Set.range U))
variable (hmul : ∀ g h, U g * U h ∈ Submodule.span ℂ (Set.range U))
variable (hstar : ∀ g, star (U g) ∈ Submodule.span ℂ (Set.range U))

theorem mem_spanGraph_iff {p : (H →L[ℂ] H) × Ultrapower σ ω} :
    p ∈ spanGraph U hone hmul hstar ↔ p ∈ Submodule.span ℂ (Set.range U) :=
  Iff.rfl

theorem generator_mem_spanGraph (g : Λ) : U g ∈ spanGraph U hone hmul hstar :=
  (mem_spanGraph_iff U hone hmul hstar).mpr (Submodule.subset_span ⟨g, rfl⟩)

/-- Finite linear combinations of generators lie in the graph. -/
theorem sum_mem_spanGraph (t : Finset Λ) (c : Λ → ℂ) :
    ∑ g ∈ t, c g • U g ∈ spanGraph U hone hmul hstar :=
  (mem_spanGraph_iff U hone hmul hstar).mpr
    (Submodule.sum_mem _ fun g _ ↦ Submodule.smul_mem _ (c g) (Submodule.subset_span ⟨g, rfl⟩))

theorem fst_sum_smul (t : Finset Λ) (c : Λ → ℂ) :
    (∑ g ∈ t, c g • U g).1 = ∑ g ∈ t, c g • (U g).1 := by
  rw [Prod.fst_sum]
  exact Finset.sum_congr rfl fun g _ ↦ Prod.smul_fst (c g) (U g)

/-- First coordinates of the graph lie in `M` once those of the generators do. -/
theorem fst_mem_of_mem_spanGraph (hUM : ∀ g, (U g).1 ∈ M) :
    ∀ p ∈ spanGraph U hone hmul hstar, p.1 ∈ M := by
  intro p hp
  have hp' : p ∈ Submodule.span ℂ (Set.range U) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hUM g
  | zero =>
    rw [Prod.fst_zero]
    exact zero_mem M
  | add x y _ _ hx hy =>
    rw [Prod.fst_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [Prod.smul_fst]
    exact M.toStarSubalgebra.smul_mem hx c

/-- The graph is trace compatible once the generators are. -/
theorem trace_of_mem_spanGraph
    (hUtr : ∀ g, ultratrace σ ω (U g).2 = ⟪τ.vec, (U g).1 τ.vec⟫_ℂ) :
    ∀ p ∈ spanGraph U hone hmul hstar, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ := by
  intro p hp
  have hp' : p ∈ Submodule.span ℂ (Set.range U) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hUtr g
  | zero =>
    rw [Prod.snd_zero, Prod.fst_zero, map_zero, _root_.zero_apply, inner_zero_right]
  | add x y _ _ hx hy =>
    rw [Prod.snd_add, Prod.fst_add, map_add, _root_.add_apply, inner_add_right, hx, hy]
  | smul c x _ hx =>
    rw [Prod.smul_snd, Prod.smul_fst, ultratrace_smul, _root_.smul_apply, inner_smul_right, hx]

/-- **Generators suffice.**  If the generator pairs have first coordinates in `M`, are trace
compatible, and finite combinations of the first coordinates are `‖·ξ‖`-dense in `M`, then there is
an injective trace-preserving `⋆`-homomorphism `M → N^ω` sending each first coordinate to the second
one. -/
theorem exists_injective_of_generators (hω : (ω : Filter ℕ) ≤ cofinite) (hUM : ∀ g, (U g).1 ∈ M)
    (hUtr : ∀ g, ultratrace σ ω (U g).2 = ⟪τ.vec, (U g).1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ t : Finset Λ, ∃ c : Λ → ℂ,
      ‖(∑ g ∈ t, c g • (U g).1 - T) τ.vec‖ < ε)
    (hsep : ∀ T ∈ M, T τ.vec = 0 → T = 0) :
    ∃ Φ : ↥M.toStarSubalgebra →⋆ₐ[ℂ] Ultrapower σ ω, Function.Injective Φ ∧
      (∀ T : ↥M.toStarSubalgebra, ultratrace σ ω (Φ T) = ⟪τ.vec, (T : H →L[ℂ] H) τ.vec⟫_ℂ) ∧
      ∀ g, Φ ⟨(U g).1, hUM g⟩ = (U g).2 := by
  have hdense' : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ spanGraph U hone hmul hstar, ‖(p.1 - T) τ.vec‖ < ε := by
    intro T hT ε hε
    obtain ⟨t, c, h⟩ := hdense T hT ε hε
    exact ⟨∑ g ∈ t, c g • U g, sum_mem_spanGraph U hone hmul hstar t c, by
      rw [fst_sum_smul]
      exact h⟩
  obtain ⟨Φ, hinj, htr, hext⟩ := exists_extension τ (spanGraph U hone hmul hstar) hω
    (fst_mem_of_mem_spanGraph U hone hmul hstar hUM)
    (trace_of_mem_spanGraph τ U hone hmul hstar hUtr) hdense' hsep
  exact ⟨Φ, hinj, htr, fun g ↦ hext (U g) (generator_mem_spanGraph U hone hmul hstar g) (hUM g)⟩

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_injective_of_generators
