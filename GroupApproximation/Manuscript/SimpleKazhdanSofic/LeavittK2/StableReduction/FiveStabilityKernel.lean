import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.Lifts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Central
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourRefinement
import GroupApproximation.Steinberg.Perfect
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel of the Leavitt refinement (lane sk-leavitt-28, part 1)

Let `R` be a ring with a Leavitt family `L`, `n ≥ 4`, `r : Fin n`, and assume a spare index
`k ≠ r` exists.  Write `D = LeavittFP.refineHom L r : St_n(R) → St_{n+1}(R)`.  This module proves
three facts about `ker D`, and one propagation fact for centrality of `K₂`.

* `ker D ≤ K₂(n, R)`, because `D` preserves and reflects `K₂`.
* `ker D ≤ ⁅St_n(R), ker D⁆`.  `D` is onto, so the Kervaire lift (rank `n + 1 ≥ 5`) splits the
  identity of `St_{n+1}(R)` through `U = St_n(R) ⧸ ⁅St_n, ker D⁆`.  By perfectness of `St_n(R)`
  and uniqueness of lifts into central extensions, the lift composed with `D` is the quotient map.
  So every `w ∈ ker D` has trivial image in `U`.
* Padding `St_n → St_{n+1}` kills `ker D`.  Padding sends `K₂(n)` into the centre (Khanh,
  Lemma 5.2, `Full.LVCentral.castSuccStab_mem_center`), so it kills `⁅St_n, ker D⁆ ⊇ ker D`.
* If `K₂(n, R)` is central, `D` is injective: the identity then kills `⁅St_n, ker D⁆ ⊇ ker D`.
* If `K₂(n, R)` is central, so is `K₂(n + 1, R)`, since `D` maps `K₂(n)` onto `K₂(n + 1)` and is
  onto.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R)

/-- An element killed by the Leavitt refinement lies in `K₂`. -/
theorem fiveStability_mem_K2_of_refineHom_eq_one {n : ℕ} (r : Fin n)
    {w : SteinbergGroup (Fin n) R} (hw : LeavittFP.refineHom L r w = 1) :
    w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R := by
  have h1 : LeavittFP.refineHom L r w ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R := by
    rw [hw]
    exact Subgroup.one_mem _
  exact LeavittFP.mem_K2_of_refineHom_mem L r h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_mem_K2_of_refineHom_eq_one

/-- **`ker D ≤ ⁅St_n, ker D⁆`** for `n ≥ 4` with a spare index.  The Kervaire lift of the
identity of `St_{n+1}(R)` into `St_n(R) ⧸ ⁅St_n, ker D⁆`, composed with `D`, is the quotient map
by uniqueness of lifts out of the perfect group `St_n(R)`. -/
theorem fiveStability_refineHom_ker_le_relCommutator {n : ℕ} (hn : 4 ≤ n) (r k : Fin n)
    (hk : k ≠ r) :
    (LeavittFP.refineHom L r).ker ≤
      Full.LVStability.relCommutator (LeavittFP.refineHom L r) := by
  haveI : Group.IsPerfect (SteinbergGroup (Fin n) R) := SteinbergGroup.fin_isPerfect (by omega)
  obtain ⟨F, hF⟩ := Full.LVStability.exists_lift_quotHom (n := n + 1) (by omega)
    (LeavittFP.refineHom L r) (LeavittFP.refineHom_surjective L r k hk)
    (MonoidHom.id (SteinbergGroup (Fin (n + 1)) R))
  have hcomp : (Full.LVStability.quotHom (LeavittFP.refineHom L r)).comp
        (F.comp (LeavittFP.refineHom L r)) =
      (Full.LVStability.quotHom (LeavittFP.refineHom L r)).comp
        (QuotientGroup.mk' (Full.LVStability.relCommutator (LeavittFP.refineHom L r))) := by
    rw [← MonoidHom.comp_assoc, hF, MonoidHom.id_comp, Full.LVStability.quotHom_comp_mk']
  have hfg := Full.LVStability.hom_eq_of_quotHom_comp_eq (LeavittFP.refineHom L r) hcomp
  intro w hw
  have hq : (QuotientGroup.mk' (Full.LVStability.relCommutator (LeavittFP.refineHom L r))) w =
      1 := by
    rw [← hfg, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hw, map_one]
  have hmem : w ∈
      (QuotientGroup.mk' (Full.LVStability.relCommutator (LeavittFP.refineHom L r))).ker :=
    MonoidHom.mem_ker.mpr hq
  rwa [QuotientGroup.ker_mk'] at hmem

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_refineHom_ker_le_relCommutator

/-- **Padding kills `ker D`.**  For `n ≥ 4` with a spare index, an element killed by the Leavitt
refinement is killed by padding `St_n(R) → St_{n+1}(R)`.  Padding sends `K₂(n)` into the centre
(`castSuccStab` is padding along `Fin.castLEEmb`, up to a proof argument), hence kills
`⁅St_n, ker D⁆ ⊇ ker D`. -/
theorem fiveStability_indexMap_eq_one_of_refineHom_eq_one {n : ℕ} (hn : 4 ≤ n) (r k : Fin n)
    (hk : k ≠ r) {w : SteinbergGroup (Fin n) R} (hw : LeavittFP.refineHom L r w = 1) :
    indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n)) w = 1 := by
  have hcen : ∀ y ∈ (LeavittFP.refineHom L r).ker,
      indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n)) y ∈
        Subgroup.center (SteinbergGroup (Fin (n + 1)) R) := by
    intro y hy
    have hy2 : y ∈ (projection (I := Fin n) (R := R)).ker :=
      fiveStability_mem_K2_of_refineHom_eq_one L r (MonoidHom.mem_ker.mp hy)
    exact Full.LVCentral.castSuccStab_mem_center hy2
  have hle := Full.LVStability.commutator_ker_le_ker (LeavittFP.refineHom L r)
    (indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n))) hcen
  exact MonoidHom.mem_ker.mp
    (hle (fiveStability_refineHom_ker_le_relCommutator L hn r k hk (MonoidHom.mem_ker.mpr hw)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_indexMap_eq_one_of_refineHom_eq_one

/-- **`D` is injective when `K₂(n)` is central.**  For `n ≥ 4` with a spare index, the identity
of `St_n(R)` is central on `ker D ≤ K₂(n)`, so it kills `⁅St_n, ker D⁆ ⊇ ker D`. -/
theorem fiveStability_eq_one_of_refineHom_eq_one {n : ℕ} (hn : 4 ≤ n) (r k : Fin n)
    (hk : k ≠ r)
    (hC : BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R))
    {w : SteinbergGroup (Fin n) R} (hw : LeavittFP.refineHom L r w = 1) : w = 1 := by
  have hcen : ∀ y ∈ (LeavittFP.refineHom L r).ker,
      MonoidHom.id (SteinbergGroup (Fin n) R) y ∈ Subgroup.center (SteinbergGroup (Fin n) R) :=
    fun y hy => hC (fiveStability_mem_K2_of_refineHom_eq_one L r (MonoidHom.mem_ker.mp hy))
  have hle := Full.LVStability.commutator_ker_le_ker (LeavittFP.refineHom L r)
    (MonoidHom.id (SteinbergGroup (Fin n) R)) hcen
  exact MonoidHom.mem_ker.mp
    (hle (fiveStability_refineHom_ker_le_relCommutator L hn r k hk (MonoidHom.mem_ker.mpr hw)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_eq_one_of_refineHom_eq_one

/-- **Centrality of `K₂` climbs one rank.**  `D` maps `K₂(n)` onto `K₂(n + 1)` and is onto, so a
central `K₂(n)` gives a central `K₂(n + 1)`. -/
theorem fiveStability_K2_le_center_succ {n : ℕ} (r k : Fin n) (hk : k ≠ r)
    (hC : BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R)) :
    BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R ≤
      Subgroup.center (SteinbergGroup (Fin (n + 1)) R) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp ((LeavittFP.K2_map_refineHom L r k hk).ge hz)
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := LeavittFP.refineHom_surjective L r k hk g
  have e := congrArg (LeavittFP.refineHom L r) (Subgroup.mem_center_iff.mp (hC hw) g')
  simpa only [map_mul] using e

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStability_K2_le_center_succ

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
