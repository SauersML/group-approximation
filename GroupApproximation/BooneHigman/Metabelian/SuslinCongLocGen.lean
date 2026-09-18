import GroupApproximation.BooneHigman.Metabelian.SuslinNormalEndpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3FamGen
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: the local normal-closure generator class

Lane `bh-met-91u`.

For commutative rings `A`, `S`, `SuslinCongLocGen A S ≤ GL₂(S)` is the NORMAL CLOSURE in
`GL₂(S)` of
* `E₂(S)`;
* every rank-one unipotent `1 + x yᵀ` with `y ⬝ᵥ x = 0` (`x y : S²`);
* every `ψ(τ)` with `ψ : A →+* S` ANY ring map and `τ ∈ SL₂(A)`.

* `suslinCongLoc_gen_le`: if `SL₃(A) = E₃(A)`, every `σ ∈ SuslinCongLocGen A S` has
  `diag(σ, 1) ∈ E₃(S)`.  Proof: `E₃(S)` is normal in `GL₃(S)` (Suslin normality, PROVED in the
  repo as `suslinNormal_elementaryGroup_normal`), so its preimage under the stabilization
  `GL₂(S) → GL₃(S)` is normal and it suffices to treat the generators: `E₂(S)` stabilizes into
  `E₃(S)`; `diag(1 + x yᵀ, 1) = 1 + (x, 0)(y, 0)ᵀ` with `(y, 0)` vanishing at the third
  coordinate and `(y, 0) ⬝ᵥ (x, 0) = 0` lies in `E₃(S)` (`suslinNormal_inE_of_dot_zero`, proved);
  `diag(ψ τ, 1) = (ψ-image of diag(τ, 1)) ∈ E₃(S)` since `diag(τ, 1) ∈ SL₃(A) = E₃(A)`.
* `suslinCongLoc_famGen_le`: for every `f : A[X] →+* S`, `f(SuslinBase3FamGen A) ⊆
  SuslinCongLocGen A S`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- `Fin 2 ⊕ Unit` has a third index avoiding any two. -/
theorem suslinCongLoc_three : ∀ p q : Fin 2 ⊕ Unit, ∃ k, k ≠ p ∧ k ≠ q := by
  rintro (p | ⟨⟩) (q | ⟨⟩)
  · exact ⟨Sum.inr (), Sum.inr_ne_inl, Sum.inr_ne_inl⟩
  · obtain ⟨p', hp'⟩ := exists_ne p
    exact ⟨Sum.inl p', fun h ↦ hp' (Sum.inl_injective h), Sum.inl_ne_inr⟩
  · obtain ⟨q', hq'⟩ := exists_ne q
    exact ⟨Sum.inl q', Sum.inl_ne_inr, fun h ↦ hq' (Sum.inl_injective h)⟩
  · exact ⟨Sum.inl 0, Sum.inl_ne_inr, Sum.inl_ne_inr⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_three

/-- The stabilization of a rank-one perturbation of `1` is a rank-one perturbation of `1`. -/
theorem suslinCongLoc_stab_val_rankOne {S : Type*} [CommRing S]
    (σ : (Matrix (Fin 2) (Fin 2) S)ˣ) (x y : Fin 2 → S)
    (hσ : (σ : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.vecMulVec x y) :
    ((stabilizeUnit (R := S) (κ := Unit) σ : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      1 + Matrix.vecMulVec (Sum.elim x 0) (Sum.elim y 0) := by
  rw [stabilizeUnit_val, hσ]
  refine Matrix.ext fun i j ↦ ?_
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
    simp [Matrix.one_apply, Matrix.vecMulVec_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_stab_val_rankOne

/-- **Rank-one unipotents stabilize into `E₃`** (over any commutative ring). -/
theorem suslinCongLoc_stab_mem_rankOne {S : Type*} [CommRing S]
    (σ : (Matrix (Fin 2) (Fin 2) S)ˣ) (x y : Fin 2 → S) (hyx : y ⬝ᵥ x = 0)
    (hσ : (σ : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.vecMulVec x y) :
    stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  have hyk : Sum.elim y (0 : Unit → S) (Sum.inr ()) = 0 := by simp
  have hyx' : Sum.elim y (0 : Unit → S) ⬝ᵥ Sum.elim x (0 : Unit → S) = 0 := by
    rw [sumElim_dotProduct_sumElim, hyx]
    simp
  obtain ⟨u, hu, hval⟩ := suslinNormal_inE_of_dot_zero (ι := Fin 2 ⊕ Unit) (A := S) hyk hyx'
  have heq : u = stabilizeUnit (R := S) (κ := Unit) σ :=
    Units.ext (hval.trans (suslinCongLoc_stab_val_rankOne σ x y hσ).symm)
  rw [← heq]
  exact hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_stab_mem_rankOne

/-- The normal closure in `GL₂(S)` of `E₂(S)`, the rank-one unipotents `1 + x yᵀ`
(`y ⬝ᵥ x = 0`) and all images `ψ(τ)`, `ψ : A →+* S`, `τ ∈ SL₂(A)`. -/
def SuslinCongLocGen (A S : Type*) [CommRing A] [CommRing S] :
    Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ :=
  Subgroup.normalClosure
    ((((elementaryGroup (Fin 2) S : Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ) :
          Set (Matrix (Fin 2) (Fin 2) S)ˣ) ∪
        {σ | ∃ x y : Fin 2 → S, y ⬝ᵥ x = 0 ∧
          (σ : Matrix (Fin 2) (Fin 2) S) = 1 + Matrix.vecMulVec x y}) ∪
      {σ | ∃ (ψ : A →+* S) (τ : (Matrix (Fin 2) (Fin 2) A)ˣ),
        Matrix.det (τ : Matrix (Fin 2) (Fin 2) A) = 1 ∧ elementaryMatrixUnitMap ψ τ = σ})

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinCongLocGen

/-- **Every element of `SuslinCongLocGen A S` stabilizes into `E₃(S)`** when `SL₃(A) = E₃(A)`. -/
theorem suslinCongLoc_gen_le {A S : Type*} [CommRing A] [CommRing S]
    (hSL : SpecialLinearInElementary A (2 + 1)) :
    SuslinCongLocGen A S ≤
      (elementaryGroup (Fin 2 ⊕ Unit) S).comap (stabilizeUnit (R := S) (κ := Unit)) := by
  have hE : (elementaryGroup (Fin 2 ⊕ Unit) S).Normal :=
    suslinNormal_elementaryGroup_normal suslinCongLoc_three
  haveI : ((elementaryGroup (Fin 2 ⊕ Unit) S).comap
      (stabilizeUnit (R := S) (κ := Unit))).Normal := hE.comap _
  refine Subgroup.normalClosure_le_normal ?_
  rintro σ ((hσ | ⟨x, y, hyx, hσ⟩) | ⟨ψ, τ, hτ, rfl⟩)
  · have hσ' : σ ∈ elementaryGroup (Fin 2) S := hσ
    change stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S
    exact (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := S) ⟨σ, hσ'⟩).2
  · change stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S
    exact suslinCongLoc_stab_mem_rankOne σ x y hyx hσ
  · change stabilizeUnit (R := S) (κ := Unit) (elementaryMatrixUnitMap ψ τ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) S
    exact suslinBase3Fam_stab_map_mem hSL ψ τ hτ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_gen_le

/-- **`SuslinBase3FamGen` maps into `SuslinCongLocGen`** along every `f : A[X] →+* S`. -/
theorem suslinCongLoc_famGen_le {A S : Type*} [CommRing A] [CommRing S] (f : A[X] →+* S) :
    SuslinBase3FamGen A ≤
      (SuslinCongLocGen A S).comap (elementaryMatrixUnitMap (ι := Fin 2) f) := by
  rw [SuslinBase3FamGen, Subgroup.closure_le]
  rintro σ (hσ | ⟨ψ, τ, hτ, rfl⟩)
  · have hσ' : σ ∈ elementaryGroup (Fin 2) A[X] := hσ
    have hloc : elementaryMatrixUnitMap f σ ∈ elementaryGroup (Fin 2) S :=
      elementaryGroup_map_le f (Subgroup.mem_map_of_mem _ hσ')
    change elementaryMatrixUnitMap f σ ∈ SuslinCongLocGen A S
    rw [SuslinCongLocGen]
    exact Subgroup.subset_normalClosure
      (Set.mem_union_left _ (Set.mem_union_left _ hloc))
  · change elementaryMatrixUnitMap f (elementaryMatrixUnitMap ψ τ) ∈ SuslinCongLocGen A S
    rw [SuslinCongLocGen]
    exact Subgroup.subset_normalClosure
      (Set.mem_union_right _ ⟨f.comp ψ, τ, hτ, (suslinBase3Fam_map_comp f ψ τ).symm⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_famGen_le

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
