import GroupApproximation.GGT.RelHypFreeProductConedFourPoint
import GroupApproximation.GGT.HullSCUnionGeometryShortBranch
import GroupApproximation.GGT.HullSCUnionGeometryFactorInput
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# Acylindricity of the coned free-product Cayley graph

For the free product `U ∗ H` relative to `U`, the relative alphabet is the
union alphabet whose `U`-factor alphabet is all of `U` and whose `H`-factor
alphabet is a finite generating set `S`.

The generic union-alphabet displacement theorem proves acylindricity once the
two factor displacement estimates are uniform.  The `H` estimate is the
proper finite-Cayley action.  The `U` estimate is vacuous past radius two,
because every element has length at most one in the alphabet `Set.univ`.
This is the acylindrical part of the Bass--Serre-tree description used in the
free-product instance of Osin's Theorem 2.4.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- Every element has word length at most one in the whole-group alphabet. -/
theorem wordNorm_setUniv_le_one {G : Type*} [Group G] (g : G) :
    wordNorm (Set.univ : Set G) g ≤ 1 :=
  wordNorm_le_one_of_mem (Set.mem_univ g)

/-- **The coned free-product action is acylindrical.**

This is the acylindricity half of the Bass--Serre free-product geometry at the
exact labelled relative generating set used by
`freeProductRelativelyHyperbolicStatement_proved`. -/
theorem isAcylindrical_freeProductLabelledRelGen
    (U H : Type) [Group U] [Group H]
    (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) :
    IsAcylindrical (CoprodI (pairFamily U H))
      (Cayley (freeProductLabelledRelGen U H S hS).alphabet) := by
  classical
  let A : Alphabet (CoprodI (pairFamily U H)) :=
    (freeProductLabelledRelGen U H S hS).alphabet
  have hfactor : ∀ b : Bool,
      IsSymmetricGeneratingSet (conedFactorAlphabet U H S b) :=
    isSymmetricGeneratingSet_conedFactorAlphabet U H hS
  have hcarrier : A.carrier =
      unionCarrier (conedFactorAlphabet U H S) := by
    change (freeProductRelGen U H S hS).alphabet.carrier = _
    exact alphabet_carrier_freeProductRelGen U H S hS
  apply HullSCUnionGeometry.isAcylindrical_cayley_of_conjDisplacement A
  intro eps heps
  let B : Alphabet H := ⟨(S : Set H), hS⟩
  have hacyB : IsAcylindrical H (Cayley B) :=
    isAcylindrical_cayley_of_finite B S.finite_toSet
  obtain ⟨RH, NH, hH⟩ :=
    HullSCUnionGeometry.exists_factorDisplacement_bound B hacyB heps
  have hfac : ∀ (b : Bool) (tau : pairFamily U H b),
      max 2 RH ≤
          ((wordNorm (conedFactorAlphabet U H S b) tau : ℕ) : ℝ) →
        {gamma : pairFamily U H b |
            ((wordNorm (conedFactorAlphabet U H S b) gamma : ℕ) : ℝ) ≤ eps ∧
            ((wordNorm (conedFactorAlphabet U H S b)
              (tau⁻¹ * gamma * tau) : ℕ) : ℝ) ≤ eps}.Finite ∧
          {gamma : pairFamily U H b |
            ((wordNorm (conedFactorAlphabet U H S b) gamma : ℕ) : ℝ) ≤ eps ∧
            ((wordNorm (conedFactorAlphabet U H S b)
              (tau⁻¹ * gamma * tau) : ℕ) : ℝ) ≤ eps}.ncard ≤ NH := by
    intro b
    cases b with
    | false =>
        intro tau htau
        have hlen : wordNorm (conedFactorAlphabet U H S false) tau ≤ 1 := by
          change wordNorm (Set.univ : Set U) tau ≤ 1
          exact wordNorm_setUniv_le_one tau
        have htwo : (2 : ℝ) ≤
            ((wordNorm (conedFactorAlphabet U H S false) tau : ℕ) : ℝ) :=
          le_trans (le_max_left 2 RH) htau
        have hone : ((wordNorm
            (conedFactorAlphabet U H S false) tau : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast hlen
        exfalso
        linarith
    | true =>
        intro tau htau
        apply hH tau
        exact le_trans (le_max_right 2 RH) htau
  obtain ⟨R, N, hRN⟩ :=
    HullSCUnionGeometry.exists_conjDisplacement_bound hfactor hcarrier heps hfac
  exact ⟨R, N, by
    intro t ht
    apply hRN t
    rwa [← hcarrier]⟩

end RelHyp
end GGT
end GroupApproximation
