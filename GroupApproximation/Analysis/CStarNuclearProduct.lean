import GroupApproximation.Analysis.BlackadarKirchbergStarEquivTransport
import GroupApproximation.Analysis.FiniteDirectSumMatrixCPRetract

/-!
# Nuclearity is preserved by finite products and star equivalence

These are the finite-dimensional permanence lemmas needed for the concrete
STW XXII algebra.  They are proved directly from the completely-positive
approximation definition in `CStarExactness`; no tensor-product
characterization or structure theorem is used.
-/

namespace GroupApproximation
namespace CStarExactness

open BlackadarKirchberg

noncomputable section

universe u v

/-- The product of two bundled finite-dimensional C-star algebras. -/
def finDimCStarAlgebraProd (D E : FinDimCStarAlgebra) : FinDimCStarAlgebra :=
  { carrier := D × E }

/-- Every finite-dimensional C-star algebra is nuclear: its identity factors
through itself. -/
theorem isNuclearCStarAlgebra_of_finiteDimensional
    (A : Type) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    IsNuclearCStarAlgebra A := by
  intro F ε hε
  let D : FinDimCStarAlgebra := { carrier := A }
  refine ⟨D, LinearMap.id, LinearMap.id, isCompletelyPositive_id,
    isCompletelyPositive_id, fun _ ↦ le_rfl, fun _ ↦ le_rfl, ?_⟩
  intro a _
  simpa using hε.le

/-- Binary products preserve the completely-positive approximation property. -/
theorem IsNuclearCStarAlgebra.prod
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (hA : IsNuclearCStarAlgebra A) (hB : IsNuclearCStarAlgebra B) :
    IsNuclearCStarAlgebra (A × B) := by
  classical
  intro F ε hε
  obtain ⟨DA, αA, βA, hαA, hβA, hαAc, hβAc, hAapp⟩ :=
    hA (F.image Prod.fst) ε hε
  obtain ⟨DB, αB, βB, hαB, hβB, hαBc, hβBc, hBapp⟩ :=
    hB (F.image Prod.snd) ε hε
  let D := finDimCStarAlgebraProd DA DB
  let α : (A × B) →ₗ[ℂ] D := prodLinearMap αA αB
  let β : D →ₗ[ℂ] (A × B) := prodLinearMap βA βB
  refine ⟨D, α, β,
    isCompletelyPositive_prodLinearMap hαA hαB,
    isCompletelyPositive_prodLinearMap hβA hβB, ?_, ?_, ?_⟩
  · intro x
    change max ‖αA x.1‖ ‖αB x.2‖ ≤ max ‖x.1‖ ‖x.2‖
    exact max_le_max (hαAc x.1) (hαBc x.2)
  · intro d
    change max ‖βA d.1‖ ‖βB d.2‖ ≤ max ‖d.1‖ ‖d.2‖
    exact max_le_max (hβAc d.1) (hβBc d.2)
  · intro x hx
    change max ‖βA (αA x.1) - x.1‖ ‖βB (αB x.2) - x.2‖ ≤ ε
    rw [max_le_iff]
    exact ⟨hAapp x.1 (Finset.mem_image_of_mem Prod.fst hx),
      hBapp x.2 (Finset.mem_image_of_mem Prod.snd hx)⟩

/-- Nuclearity transports across a star-algebra equivalence. -/
theorem IsNuclearCStarAlgebra.of_starAlgEquiv
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) (hB : IsNuclearCStarAlgebra B) :
    IsNuclearCStarAlgebra A := by
  classical
  intro F ε hε
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ :=
    hB (F.image e) ε hε
  let down : A →ₗ[ℂ] D :=
    α.comp (BlackadarKirchberg.starAlgEquivLinearMap e)
  let up : D →ₗ[ℂ] A :=
    (BlackadarKirchberg.starAlgEquivLinearMap e.symm).comp β
  refine ⟨D, down, up,
    BlackadarKirchberg.isCompletelyPositive_comp_starAlgEquiv e α hα,
    (isCompletelyPositive_of_starAlgHom
      e.symm.toStarAlgHom.toNonUnitalStarAlgHom).comp hβ, ?_, ?_, ?_⟩
  · intro a
    change ‖α (e a)‖ ≤ ‖a‖
    calc
      ‖α (e a)‖ ≤ ‖e a‖ := hαc (e a)
      _ = ‖a‖ := StarAlgEquiv.norm_map e a
  · intro d
    change ‖e.symm (β d)‖ ≤ ‖d‖
    rw [StarAlgEquiv.norm_map]
    exact hβc d
  · intro a ha
    change ‖e.symm (β (α (e a))) - a‖ ≤ ε
    calc
      ‖e.symm (β (α (e a))) - a‖ =
          ‖e.symm (β (α (e a)) - e a)‖ := by
            rw [map_sub, e.symm_apply_apply]
      _ = ‖β (α (e a)) - e a‖ := StarAlgEquiv.norm_map e.symm _
      _ ≤ ε := happ (e a) (Finset.mem_image_of_mem e ha)

/-- Split a dependent product over `Fin (n+1)` into its first coordinate and
the product over the remaining coordinates. -/
def piFinSuccStarAlgEquiv (n : ℕ) (A : Fin (n + 1) → Type)
    [∀ i, CStarAlgebra (A i)] :
    (∀ i, A i) ≃⋆ₐ[ℂ] (A 0 × ∀ i : Fin n, A i.succ) where
  toFun x := (x 0, fun i ↦ x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl
  map_star' x := by ext <;> rfl

/-- A finite dependent product of nuclear unital C-star algebras is nuclear. -/
theorem isNuclearCStarAlgebra_piFin (n : ℕ) (A : Fin n → Type)
    [∀ i, CStarAlgebra (A i)]
    (hA : ∀ i, IsNuclearCStarAlgebra (A i)) :
    IsNuclearCStarAlgebra (∀ i, A i) := by
  induction n with
  | zero =>
      exact isNuclearCStarAlgebra_of_finiteDimensional (∀ i : Fin 0, A i)
  | succ n ih =>
      let tail : Fin n → Type := fun i ↦ A i.succ
      have htail : IsNuclearCStarAlgebra (∀ i, tail i) :=
        ih tail (fun i ↦ hA i.succ)
      exact IsNuclearCStarAlgebra.of_starAlgEquiv
        (piFinSuccStarAlgEquiv n A) ((hA 0).prod htail)

end

end CStarExactness
end GroupApproximation
