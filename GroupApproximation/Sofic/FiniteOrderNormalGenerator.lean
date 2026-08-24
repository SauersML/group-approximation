import GroupApproximation.Sofic.ActiveCoreAlmostRepresentation
import GroupApproximation.Sofic.FiniteGroupCoronaExactification
import GroupApproximation.Sofic.OpToHSShadowResidual

/-!
# Finite-order normal generators and the MF radical

The main theorem in this file identifies MF invisibility with universal
Hilbert--Schmidt invisibility for a finite-order normal generator of a finitely
generated group.  Its analytic engine is quantitative active-core reblocking.
-/

namespace GroupApproximation
namespace FiniteOrderNormalGenerator

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G]
variable {X : ℕ → FiniteModel}

/-- Evaluation of an ambient packet word commutes with passage to the norm
matrix corona. -/
theorem quotient_mk_ambientWord
    {I : Type*} [Fintype I] [DecidableEq I] [∀ n, Nonempty (X n)]
    (W : ∀ n, I → Matrix.unitaryGroup (X n) ℂ)
    (l : List I) :
    (QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l) :
        NormMatrixCoronaUnitary X) =
      (l.map fun g ↦
        (QuotientGroup.mk (fun n ↦ W n g) : NormMatrixCoronaUnitary X)).prod := by
  induction l with
  | nil =>
      change QuotientGroup.mk (1 : ∀ n, Matrix.unitaryGroup (X n) ℂ) = 1
      exact map_one (QuotientGroup.mk' (nullCofiniteOpSubgroup X))
  | cons i l ih =>
      change QuotientGroup.mk
          ((fun n ↦ W n i) *
            (fun n ↦ TorsionActiveCore.ambientWord (W n) l)) = _
      rw [QuotientGroup.mk_mul, ih]
      rfl

set_option maxHeartbeats 400000 in
/-- Coordinate packet lifts of a corona representation respect every group
word relation in operator norm. -/
theorem ambientWordsRespectGroup_of_corona
    [∀ n, Nonempty (X n)] (S : Finset G)
    (rho : G →* NormMatrixCoronaUnitary X)
    (W : ∀ n, S → Matrix.unitaryGroup (X n) ℂ)
    (hW : ∀ i : S, QuotientGroup.mk (fun n ↦ W n i) = rho i) :
    ActiveCoreAlmostRepresentation.AmbientWordsRespectGroup S W := by
  classical
  intro l₁ l₂ heval ε hε
  have hclass :
      (QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l₁) :
          NormMatrixCoronaUnitary X) =
        QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l₂) := by
    rw [quotient_mk_ambientWord W, quotient_mk_ambientWord W]
    simp_rw [hW]
    change (l₁.map (rho ∘ fun i : S ↦ (i : G))).prod =
      (l₂.map (rho ∘ fun i : S ↦ (i : G))).prod
    simpa only [map_list_prod, List.map_map] using congrArg rho heval
  have hnull :
      (fun n ↦ TorsionActiveCore.ambientWord (W n) l₁)⁻¹ *
          (fun n ↦ TorsionActiveCore.ambientWord (W n) l₂) ∈
        nullCofiniteOpSubgroup X := QuotientGroup.eq.mp hclass
  have hev := hnull ε hε
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  change opLength (X n)
    ((TorsionActiveCore.ambientWord (W n) l₁)⁻¹ *
      TorsionActiveCore.ambientWord (W n) l₂) < ε at this
  rw [opLength_inv_mul] at this
  rw [norm_sub_rev]
  exact this.le

omit [Group G] in
/-- Conjugate-product evaluation commutes with passage to the norm matrix
corona. -/
theorem quotient_mk_conjugateWord
    [∀ n, Nonempty (X n)]
    (R : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (C : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (l : List (G × Bool)) :
    (QuotientGroup.mk (fun n ↦ TorsionActiveCore.conjugateWord (R n)
        (l.map fun p ↦ (C p.1 n, p.2))) : NormMatrixCoronaUnitary X) =
      ConjWord.conjWord
        (QuotientGroup.mk R : NormMatrixCoronaUnitary X)
        (l.map fun p ↦
          ((QuotientGroup.mk (C p.1) : NormMatrixCoronaUnitary X), p.2)) := by
  induction l with
  | nil =>
      change QuotientGroup.mk (1 : ∀ n, Matrix.unitaryGroup (X n) ℂ) = 1
      exact map_one (QuotientGroup.mk' (nullCofiniteOpSubgroup X))
  | cons p l ih =>
      obtain ⟨c, positive⟩ := p
      simp only [List.map_cons]
      rw [ConjWord.conjWord_cons]
      change QuotientGroup.mk
        ((fun n ↦ TorsionActiveCore.conjugateFactor (R n) (C c n) positive) *
          (fun n ↦ TorsionActiveCore.conjugateWord (R n)
            (l.map fun p ↦ (C p.1 n, p.2)))) = _
      rw [QuotientGroup.mk_mul, ih]
      unfold TorsionActiveCore.conjugateFactor
      cases positive <;> rfl

/-- A conjugate-word packet built from coordinate lifts represents the chosen
finite generating packet in the corona. -/
theorem quotient_mk_conjugateWordPacket
    [∀ n, Nonempty (X n)] (S : Finset G) (a : G)
    (words : S → List (G × Bool))
    (hwords : ∀ i : S, ConjWord.conjWord a (words i) = i)
    (rho : G →* NormMatrixCoronaUnitary X)
    (R : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hR : QuotientGroup.mk R = rho a)
    (C : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hC : ∀ g, QuotientGroup.mk (C g) = rho g) (i : S) :
    QuotientGroup.mk (fun n ↦
        TorsionActiveCore.conjugateWordPacket (R n)
          (fun j : S ↦ (words j).map fun p ↦ (C p.1 n, p.2)) i) = rho i := by
  change QuotientGroup.mk (fun n ↦ TorsionActiveCore.conjugateWord (R n)
      ((words i).map fun p ↦ (C p.1 n, p.2))) = rho i
  rw [quotient_mk_conjugateWord R C (words i), hR]
  simp_rw [hC]
  rw [← ConjWord.map_conjWord]
  rw [hwords]

end

end FiniteOrderNormalGenerator
end GroupApproximation
