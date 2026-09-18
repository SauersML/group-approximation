import GroupApproximation.BooneHigman.Metabelian.SuslinNormalLemma
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin normality, part 4: `E_n(A) ⊴ GL_n(A)` for `n ≥ 3`

Lane `bh-met-39b`.  **Suslin's normality theorem** (A. A. Suslin, 1977): over a commutative
ring `A` and for `n ≥ 3`, the elementary group `E_n(A)` is normal in `GL_n(A)`.

For `g ∈ GL_n(A)` put `G = g`, `H = g⁻¹`.  Then
`g x_{ij}(a) g⁻¹ = 1 + v wᵀ` with `v = G e_i`, `wᵀ = a e_jᵀ H`
(`suslinNormal_conj_single`), and `uᵀ v = 1`, `wᵀ v = 0` for `uᵀ = e_iᵀ H`.  Suslin's lemma
(`suslinNormal_inE_of_unimodular`) gives `g x_{ij}(a) g⁻¹ ∈ E_n(A)`, and the conjugation
closure passes from the generators to all of `E_n(A)` by closure induction.

Endpoints: `suslinNormal_elementaryGroup_normal` (any index type in which every two indices
avoid a third), `suslinNormal_elementaryGroup_normal_fin` (`Fin N`, `2 < N`) and the
Statement `SuslinNormalStatement` with its proof `suslinNormalStatement_holds`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

universe u

section Endpoint

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- `G (1 + a E_{ij}) H = 1 + (G e_i)(a e_jᵀ H)` when `G H = 1`. -/
theorem suslinNormal_conj_single {G H : Matrix ι ι A} (hGH : G * H = 1) (i j : ι) (a : A) :
    G * (1 + Matrix.single i j a) * H =
      1 + Matrix.vecMulVec (Matrix.mulVec G (Pi.single i 1))
        (Matrix.vecMul (Pi.single j a) H) := by
  have hs : Matrix.single i j a = Matrix.vecMulVec (Pi.single i 1) (Pi.single j a) := by
    rw [suslinNormal_vecMulVec_single_single, one_mul]
  rw [hs, mul_add, mul_one, add_mul, hGH, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_conj_single

/-- Conjugates of elementary generators are elementary. -/
theorem suslinNormal_conj_elementaryUnit_mem (h3 : ∀ p q : ι, ∃ k, k ≠ p ∧ k ≠ q)
    (i j : ι) (h : i ≠ j) (a : A) (g : (Matrix ι ι A)ˣ) :
    g * elementaryUnit i j h a * g⁻¹ ∈ elementaryGroup ι A := by
  have hHG : ((g⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) * (g : Matrix ι ι A) = 1 :=
    Units.inv_mul g
  have hconj : ((g * elementaryUnit i j h a * g⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) =
      1 + Matrix.vecMulVec (Matrix.mulVec (g : Matrix ι ι A) (Pi.single i 1))
        (Matrix.vecMul (Pi.single j a) ((g⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A)) := by
    rw [Units.val_mul, Units.val_mul]
    exact suslinNormal_conj_single (Units.mul_inv g) i j a
  have huv : Matrix.vecMul (Pi.single i (1 : A)) ((g⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) ⬝ᵥ
      Matrix.mulVec (g : Matrix ι ι A) (Pi.single i 1) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec,
      single_dotProduct, Pi.single_eq_same, one_mul]
  have hwv : Matrix.vecMul (Pi.single j a) ((g⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) ⬝ᵥ
      Matrix.mulVec (g : Matrix ι ι A) (Pi.single i 1) = 0 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec,
      single_dotProduct, Pi.single_eq_of_ne' h, mul_zero]
  obtain ⟨z, hz, hzval⟩ := suslinNormal_inE_of_unimodular h3 _ _ _ huv hwv
  have hzeq : z = g * elementaryUnit i j h a * g⁻¹ := Units.ext (hzval.trans hconj.symm)
  rw [← hzeq]
  exact hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_conj_elementaryUnit_mem

/-- **Suslin's normality theorem.**  If every two indices avoid a third (`|ι| ≥ 3`), the
elementary group `E_ι(A)` is normal in `GL_ι(A)` for every commutative ring `A`. -/
theorem suslinNormal_elementaryGroup_normal (h3 : ∀ p q : ι, ∃ k, k ≠ p ∧ k ≠ q) :
    (elementaryGroup ι A).Normal := by
  refine ⟨fun n hn => ?_⟩
  have hn' : n ∈ Subgroup.closure
      {z | ∃ (i j : ι) (h : i ≠ j) (a : A), elementaryUnit i j h a = z} := hn
  refine Subgroup.closure_induction (p := fun x _ => ∀ g : (Matrix ι ι A)ˣ,
      g * x * g⁻¹ ∈ elementaryGroup ι A) ?_ ?_ ?_ ?_ hn'
  · rintro x ⟨i, j, h, a, rfl⟩ g
    exact suslinNormal_conj_elementaryUnit_mem h3 i j h a g
  · intro g
    rw [mul_one, mul_inv_cancel]
    exact (elementaryGroup ι A).one_mem
  · intro x y _ _ hx hy g
    have hxy := (elementaryGroup ι A).mul_mem (hx g) (hy g)
    have heq : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    rwa [heq] at hxy
  · intro x _ hx g
    have hinv := (elementaryGroup ι A).inv_mem (hx g)
    have heq : (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := by group
    rwa [heq] at hinv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_elementaryGroup_normal

end Endpoint

/-- **Suslin's normality theorem**, rank `N ≥ 3`. -/
theorem suslinNormal_elementaryGroup_normal_fin {A : Type*} [CommRing A] (N : ℕ)
    (hN : 2 < N) : (elementaryGroup (Fin N) A).Normal :=
  suslinNormal_elementaryGroup_normal (fun p q => Fin.exists_ne_and_ne_of_two_lt p q hN)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_elementaryGroup_normal_fin

/-- **Statement** (Suslin 1977): for every commutative ring `A` and `N ≥ 3`, the elementary
group `E_N(A)` is normal in `GL_N(A)`. -/
def SuslinNormalStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ), 2 < N → (elementaryGroup (Fin N) A).Normal

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinNormalStatement

theorem suslinNormalStatement_holds : SuslinNormalStatement.{u} := by
  intro A _ N hN
  exact suslinNormal_elementaryGroup_normal_fin (A := A) N hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormalStatement_holds

/-- Conjugation form, for consumers: `g ε g⁻¹ ∈ E_N(A)` for `ε ∈ E_N(A)`, `g ∈ GL_N(A)`. -/
theorem suslinNormal_conj_mem {A : Type*} [CommRing A] {N : ℕ} (hN : 2 < N)
    {ε : Matrix.GeneralLinearGroup (Fin N) A} (hε : ε ∈ elementaryGroup (Fin N) A)
    (g : Matrix.GeneralLinearGroup (Fin N) A) : g * ε * g⁻¹ ∈ elementaryGroup (Fin N) A :=
  (suslinNormal_elementaryGroup_normal_fin N hN).conj_mem ε hε g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_conj_mem

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
