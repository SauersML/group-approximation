import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.InternalRadicalGap

/-!
# Normal property-(T) subgroups in the compression defect

Finiteness, centrality, and torsion are not needed for the basic non-MF
obstruction.  A second Kazhdan corner replaces the finite subgroup average.

Assume that a nontrivial normal property-`(T)` subgroup `K` of `E` lies in
the compression-defect normal closure.  If `E` had a weak-MF approximation,
the normal-Kazhdan corner construction would produce an ambient tracial
ultraproduct representation in which some element of `K` survives.  The
first Kazhdan compressor, applied to that same corner model, kills all
compression defects and hence their normal closure.  It therefore kills
every element of `K`, a contradiction.

This theorem is the torsion-free analytic core.  Its stronger elementwise
MF-radical form additionally requires converting an arbitrary surviving
norm-ultraproduct image into a uniformly separated weak-MF approximation;
that marked amplification is developed separately.
-/

namespace GroupApproximation
namespace KazhdanCompressionCore

open Filter
open scoped commutatorElement

variable {Γ E : Type} [Group Γ] [Group E]

/-- The scheduled normal Kazhdan corner, regarded as an operator-norm almost
representation of the ambient group. -/
noncomputable def normalCornerOpAlmostRepresentation
    {A : WeakMFApproximation E} {K : Subgroup E} [K.Normal] [Nontrivial K]
    {D : InternalRadicalGap.Setup A K}
    (R : InternalRadicalGap.AmbientMovingCornerSchedule A K D) :
    OpAlmostRepresentation E where
  model := R.model
  modelNonempty := R.model_nonempty
  map := R.map
  asymptoticallyMultiplicative := R.map_multiplicative_eventually_op

/-- **Normal-Kazhdan compression obstruction.**  A nontrivial normal
property-`(T)` subgroup contained in the compression defect prevents weak-MF
approximation.  The subgroup may be infinite, noncentral, and torsion-free. -/
theorem not_isWeakMF_of_normalKazhdan_le_defect
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (K : Subgroup E) [K.Normal] [Nontrivial K]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal) :
    ¬ IsWeakMF E := by
  classical
  intro hMF
  obtain ⟨separation, hseparation, happroximation⟩ := hMF
  let A : WeakMFApproximation E :=
    Classical.choice
      (exists_weakMFApproximation hseparation happroximation)
  obtain ⟨D⟩ := InternalRadicalGap.exists_setup A K hT
  obtain ⟨R⟩ := InternalRadicalGap.exists_ambientMovingCornerSchedule A K D
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let B : OpAlmostRepresentation E := normalCornerOpAlmostRepresentation R
  let S := toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hdefect : ∀ gamma : Γ,
      rhoHS ⁅C.transported, C.iota gamma⁆ = 1 := by
    intro gamma
    exact C.compressionDefects_eq_one_in_hyperlinearHom B hcof gamma
  have hkillK : ∀ x : K, rhoHS (x : E) = 1 := by
    intro x
    exact C.map_eq_one_of_mem_of_defects_eq_one rhoHS hdefect K hK x
  obtain ⟨s, hs, hsurvive⟩ :=
    R.exists_generator_hyperlinearHom_ne_one hcof
  apply hsurvive
  rw [R.hyperlinearHom_apply]
  have hkill := hkillK s
  change QuotientGroup.mk (fun n ↦ S.map n (s : E)) = 1 at hkill
  have hmap : (fun n ↦ S.map n (s : E)) = (fun n ↦ R.map n (s : E)) := by
    funext n
    rfl
  rw [hmap] at hkill
  exact hkill

end KazhdanCompressionCore
end GroupApproximation
