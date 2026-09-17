import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: completeness and direct sums

* `isCompleteModule_prod`: `E ⊕ F` is complete when `E` and `F` are.
* `isCompleteModule_of_unitary`: if `F ⊕ E ≅ G` unitarily and `G` is complete, then
  `E` is complete.

The second result is the necessity half of the truth check in `Basic`. A stabilization
unitary `H_B ⊕ E → H_B` exists only for complete `E`, so the completeness hypothesis
in the corrected statement cannot be dropped.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **A direct sum of complete modules is complete.** -/
theorem isCompleteModule_prod {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
    (hE : IsCompleteModule E) (hF : IsCompleteModule F) :
    IsCompleteModule (prod E F) := by
  intro u hu
  have h1 : IsCauchy E fun n => (u n).1 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m n hm hn => le_trans (norm_fst_le (u m - u n)) (hN m n hm hn)⟩
  have h2 : IsCauchy F fun n => (u n).2 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m n hm hn => le_trans (norm_snd_le (u m - u n)) (hN m n hm hn)⟩
  obtain ⟨y₁, hy₁⟩ := hE _ h1
  obtain ⟨y₂, hy₂⟩ := hF _ h2
  refine ⟨(y₁, y₂), fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hy₁ (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hy₂ (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have ha : E.norm ((u n).1 - y₁) ≤ ε / 2 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hb : F.norm ((u n).2 - y₂) ≤ ε / 2 := hN₂ n (le_trans (le_max_right _ _) hn)
  calc (prod E F).norm (u n - (y₁, y₂))
      ≤ E.norm (u n - (y₁, y₂)).1 + F.norm (u n - (y₁, y₂)).2 := norm_prod_le _
    _ ≤ ε / 2 + ε / 2 := add_le_add ha hb
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isCompleteModule_prod

/-- **A summand of a complete module, split off by a unitary, is complete.** -/
theorem isCompleteModule_of_unitary {F : CStarModule.{v, w} B} {E : CStarModule.{v, w'} B}
    {G : CStarModule.{v, w''} B} (U : Adjointable (prod F E) G) (hU : U.IsUnitaryAdj)
    (hG : IsCompleteModule G) : IsCompleteModule E := by
  intro u hu
  let z : ℕ → (prod F E).carrier := fun n => ((0 : F.carrier), u n)
  have hsub : ∀ m n : ℕ, z m - z n = ((0 : F.carrier), u m - u n) :=
    fun m n => Prod.ext (sub_self (0 : F.carrier)) rfl
  have hv : IsCauchy G fun n => U.toFun (z n) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have h := hU.norm_map (z m - z n)
    rw [hsub m n, Adjointable.norm_inr, U.map_sub] at h
    show G.norm (U.toFun (z m) - U.toFun (z n)) ≤ ε
    rw [h]
    exact hN m n hm hn
  obtain ⟨w, hw⟩ := hG _ hv
  refine ⟨(U.adj w).2, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hw ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hback : (Adjointable.adjoint U).toFun (U.toFun (z n) - w) = z n - U.adj w := by
    rw [Adjointable.map_sub]
    exact congrArg (fun p : (prod F E).carrier => p - U.adj w) (hU.adj_toFun (z n))
  have hnorm : (prod F E).norm (z n - U.adj w) = G.norm (U.toFun (z n) - w) := by
    rw [← hback]
    exact hU.adjoint.norm_map _
  calc E.norm (u n - (U.adj w).2) = E.norm (z n - U.adj w).2 := rfl
    _ ≤ (prod F E).norm (z n - U.adj w) := norm_snd_le _
    _ = G.norm (U.toFun (z n) - w) := hnorm
    _ ≤ ε := hN n hn

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isCompleteModule_of_unitary

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
