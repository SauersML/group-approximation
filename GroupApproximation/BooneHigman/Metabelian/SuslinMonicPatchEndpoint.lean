import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatchFin
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Statement
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalPatch
import GroupApproximation.BooneHigman.Metabelian.SuslinCongIndEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# `suslinMonic_PatchStatement` holds unconditionally

Lane `bh-met-93n`.  The local-global principle `suslinMonicPatch_localGlobal_fin`
(`SuslinMonicPatchFin.lean`) is transported from `Fin N` to an arbitrary finite index type `ι`
with `2 < |ι|` along `Fintype.equivFin ι` (`suslinMonicPatch_localGlobal`), and applied to
`ι = Fin 2 ⊕ Unit` after commuting `stabilizeUnit` with the coefficient maps.  This proves
`suslinMonic_PatchStatement` (`suslinMonicPatch_patchStatement`), hence, through
`suslinMonicLocal_global_of_patch`, `suslinCongInd_MonicStatement`
(`suslinMonicPatch_monicStatement`), and discharges the `hM` hypothesis of the consumers in
`SuslinCongIndEndpoint.lean`.  The determinant and leading-coefficient hypotheses of the
patch Statement are not needed.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- Reindexing maps `E_ι` into `E_κ`. -/
theorem suslinMonicPatch_reindex_mem {S ι κ : Type*} [CommRing S] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {u : (Matrix ι ι S)ˣ}
    (hu : u ∈ elementaryGroup ι S) :
    elementaryReindexUnitEquiv (R := S) e u ∈ elementaryGroup κ S := by
  rw [← elementaryReindexGroup_map (R := S) e]
  exact Subgroup.mem_map_of_mem _ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_reindex_mem

/-- A unit whose reindexing lies in `E_κ` lies in `E_ι`. -/
theorem suslinMonicPatch_mem_of_reindex_mem {S ι κ : Type*} [CommRing S] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {u : (Matrix ι ι S)ˣ}
    (hu : elementaryReindexUnitEquiv (R := S) e u ∈ elementaryGroup κ S) :
    u ∈ elementaryGroup ι S := by
  rw [← elementaryReindexGroup_map (R := S) e, Subgroup.mem_map] at hu
  obtain ⟨v, hv, hve⟩ := hu
  have hve' : elementaryReindexUnitEquiv (R := S) e v = elementaryReindexUnitEquiv (R := S) e u :=
    hve
  rw [← (elementaryReindexUnitEquiv (R := S) e).injective hve']
  exact hv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_mem_of_reindex_mem

/-- **Suslin's local-global principle for `E_ι`, `|ι| > 2`**, over every commutative ring. -/
theorem suslinMonicPatch_localGlobal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 2 < Fintype.card ι) {A : Type*} [CommRing A] (τ : (Matrix ι ι A[X])ˣ)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) τ ∈
      elementaryGroup ι A)
    (hloc : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      elementaryMatrixUnitMap
          (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
        elementaryGroup ι (Polynomial (Localization.AtPrime 𝔪))) :
    τ ∈ elementaryGroup ι A[X] := by
  refine suslinMonicPatch_mem_of_reindex_mem (Fintype.equivFin ι) ?_
  refine suslinMonicPatch_localGlobal_fin hι _ ?_ ?_
  · rw [suslinBase3_map_reindex]
    exact suslinMonicPatch_reindex_mem _ h0
  · intro 𝔪 h𝔪
    rw [suslinBase3_map_reindex]
    exact suslinMonicPatch_reindex_mem _ (hloc 𝔪 h𝔪)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_localGlobal

/-- **`suslinMonic_PatchStatement` holds**, unconditionally. -/
theorem suslinMonicPatch_patchStatement : suslinMonic_PatchStatement := by
  intro R _ τ _ _ hconst hloc
  refine suslinMonicPatch_localGlobal (ι := Fin 2 ⊕ Unit) (by simp) _ ?_ ?_
  · rw [suslinBase3_map_stabilize]
    exact hconst
  · intro 𝔪 h𝔪
    rw [suslinBase3_map_stabilize]
    exact hloc 𝔪 h𝔪

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_patchStatement

/-- **`suslinCongInd_MonicStatement` holds**, unconditionally. -/
theorem suslinMonicPatch_monicStatement : suslinCongInd_MonicStatement :=
  suslinMonicLocal_global_of_patch suslinMonicPatch_patchStatement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_monicStatement

/-- `suslinCongInd_stabLocal_charP` without the monic hypothesis. -/
theorem suslinMonicPatch_stabLocal_charP (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') :
    SuslinBase3StabLocal (Chain.CharPPoly p k) 2 :=
  suslinCongInd_stabLocal_charP suslinMonicPatch_monicStatement p k hA

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_stabLocal_charP

/-- `suslinCongInd_powStab_charP` without the monic hypothesis. -/
theorem suslinMonicPatch_powStab_charP (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hA : ∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') :
    SuslinBase3CongPowStab (Chain.CharPPoly p k) 2 :=
  suslinCongInd_powStab_charP suslinMonicPatch_monicStatement p k hA

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_powStab_charP

/-- `suslinCongInd_global_of_monic` without the monic hypothesis. -/
theorem suslinMonicPatch_global (hZ : ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2) :
    SuslinBase3GlobalStatement :=
  suslinCongInd_global_of_monic suslinMonicPatch_monicStatement hZ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_global

/-- `suslinCongInd_indBase_of_monic` without the monic hypothesis. -/
theorem suslinMonicPatch_indBase (hZ : ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2) :
    SuslinR2IndBaseStatement :=
  suslinCongInd_indBase_of_monic suslinMonicPatch_monicStatement hZ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_indBase

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
