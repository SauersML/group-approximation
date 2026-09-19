/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Restrict
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Adding one vertex is a retract amalgam (Step 6)

Let `v ∉ s`, and put `c = s ∩ lk(v)`. Then `GP (insert v s)` embeds in the retract amalgam
`GP s *_(GP c) (GP c × G v)`, where `GP c` is a retract of `GP s` (`gpIncl`, `gpRestr`). The
embedding is `gpToAmalg`, with left inverse `amalgToGp` (`amalgToGp_gpToAmalg`).

Then `question31_of_retractAmalgamClosure`: induction over the vertices gives
`RetractAmalgamClosure → Question31`. This file has no literature inputs.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace GroupApproximation.BHPalomar.GraphProducts

noncomputable section

open Monoid

variable {V : Type} (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)]

/-- The link of `v` inside `s`. -/
abbrev linkIn (s : Set V) (v : V) : Set V := s ∩ Γ.neighborSet v

theorem linkIn_subset (s : Set V) (v : V) : linkIn Γ s v ⊆ s := Set.inter_subset_left

theorem subset_insert' (s : Set V) (v : V) : s ⊆ insert v s := Set.subset_insert v s

/-- The amalgam `GP s *_(GP c) (GP c × G v)`. -/
abbrev AmalgV (s : Set V) (v : V) :=
  RetractAmalgam (gpIncl (Γ := Γ) (G := G) (linkIn_subset Γ s v)) (G v)

/-- The quotient map onto the amalgam. -/
abbrev amk (s : Set V) (v : V) :
    Coprod (GP Γ G s) (GP Γ G (linkIn Γ s v) × G v) →* AmalgV Γ G s v :=
  QuotientGroup.mk' _

theorem amk_rel (s : Set V) (v : V) (x : GP Γ G (linkIn Γ s v)) :
    amk Γ G s v (Coprod.inl (gpIncl (linkIn_subset Γ s v) x)) = amk Γ G s v (Coprod.inr (x, 1)) := by
  have h1 : amk Γ G s v (Coprod.inl (gpIncl (linkIn_subset Γ s v) x) * (Coprod.inr (x, 1))⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

/-- The vertex maps of `GP (insert v s) → amalgam`. -/
def toAmalgFam (s : Set V) (v : V) : ∀ u, G u →* AmalgV Γ G s v :=
  Function.update
    (fun u => if u ∈ s then (amk Γ G s v).comp (Coprod.inl.comp (gpOf Γ G s u)) else 1)
    v ((amk Γ G s v).comp (Coprod.inr.comp (MonoidHom.inr _ _)))

theorem toAmalgFam_v (s : Set V) (v : V) (a : G v) :
    toAmalgFam Γ G s v v a = amk Γ G s v (Coprod.inr (1, a)) := by
  simp [toAmalgFam, Function.update_self]

theorem toAmalgFam_s (s : Set V) (v : V) {u : V} (huv : u ≠ v) (hu : u ∈ s) (a : G u) :
    toAmalgFam Γ G s v u a = amk Γ G s v (Coprod.inl (gpOf Γ G s u a)) := by
  simp [toAmalgFam, Function.update_of_ne huv, hu]

theorem toAmalgFam_out (s : Set V) (v : V) {u : V} (huv : u ≠ v) (hu : u ∉ s) (a : G u) :
    toAmalgFam Γ G s v u a = 1 := by
  simp [toAmalgFam, Function.update_of_ne huv, hu]

/-- A vertex group of the link commutes with `G v` in the amalgam. -/
theorem link_comm (s : Set V) (v : V) {w : V} (hw : w ∈ linkIn Γ s v) (b : G w) (a : G v) :
    amk Γ G s v (Coprod.inr (1, a)) * amk Γ G s v (Coprod.inl (gpOf Γ G s w b)) =
      amk Γ G s v (Coprod.inl (gpOf Γ G s w b)) * amk Γ G s v (Coprod.inr (1, a)) := by
  rw [← gpIncl_of (linkIn_subset Γ s v) hw, amk_rel, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  ext <;> simp

theorem toAmalg_comm (s : Set V) (v : V) (u w : V) (hadj : Γ.Adj u w)
    (hu : u ∈ insert v s) (hw : w ∈ insert v s) (a : G u) (b : G w) :
    toAmalgFam Γ G s v u a * toAmalgFam Γ G s v w b =
      toAmalgFam Γ G s v w b * toAmalgFam Γ G s v u a := by
  have hne : u ≠ w := hadj.ne
  by_cases huv : u = v
  · cases huv
    have hwv := hne.symm
    have hws : w ∈ s := (Set.mem_insert_iff.mp hw).resolve_left hwv
    have hwc := (⟨hws, hadj⟩ : w ∈ linkIn Γ s _)
    rw [toAmalgFam_v, toAmalgFam_s Γ G s _ hwv hws]
    exact link_comm Γ G s _ hwc b a
  · have hus : u ∈ s := (Set.mem_insert_iff.mp hu).resolve_left huv
    by_cases hwv : w = v
    · cases hwv
      have huc := (⟨hus, hadj.symm⟩ : u ∈ linkIn Γ s _)
      rw [toAmalgFam_v, toAmalgFam_s Γ G s _ huv hus]
      exact (link_comm Γ G s _ huc a b).symm
    · have hws : w ∈ s := (Set.mem_insert_iff.mp hw).resolve_left hwv
      rw [toAmalgFam_s Γ G s v huv hus, toAmalgFam_s Γ G s v hwv hws, ← map_mul, ← map_mul,
        ← map_mul, ← map_mul, gpOf_comm s hadj a b]

/-- `GP (insert v s) → GP s *_(GP c) (GP c × G v)`. -/
def gpToAmalg (s : Set V) (v : V) : GP Γ G (insert v s) →* AmalgV Γ G s v :=
  gpLift (insert v s) (toAmalgFam Γ G s v)
    (fun u hu a => by
      have huv : u ≠ v := fun h => hu (by rw [h]; exact Set.mem_insert v s)
      have hus : u ∉ s := fun h => hu (Set.mem_insert_of_mem v h)
      exact toAmalgFam_out Γ G s v huv hus a)
    (toAmalg_comm Γ G s v)

/-- Elements of `GP c` commute with `G v` in `GP (insert v s)`. -/
theorem incl_link_comm (s : Set V) (v : V) (x : GP Γ G (linkIn Γ s v)) (a : G v) :
    Commute (gpIncl ((linkIn_subset Γ s v).trans (subset_insert' s v)) x)
      (gpOf Γ G (insert v s) v a) := by
  induction x using gp_induction with
  | one =>
    rw [map_one]
    exact Commute.one_left _
  | of u b =>
    by_cases hu : u ∈ linkIn Γ s v
    · rw [gpIncl_of _ hu]
      exact gpOf_comm (insert v s) (show Γ.Adj v u from hu.2).symm b a
    · rw [gpIncl_of_not _ hu]
      exact Commute.one_left _
  | mul x y hx hy =>
    rw [map_mul]
    exact hx.mul_left hy

/-- The `GP c × G v` side of the inverse. -/
def amalgRight (s : Set V) (v : V) : GP Γ G (linkIn Γ s v) × G v →* GP Γ G (insert v s) :=
  MonoidHom.noncommCoprod (gpIncl ((linkIn_subset Γ s v).trans (subset_insert' s v)))
    (gpOf Γ G (insert v s) v) (incl_link_comm Γ G s v)

/-- `GP s *_(GP c) (GP c × G v) → GP (insert v s)`. -/
def amalgToGp (s : Set V) (v : V) : AmalgV Γ G s v →* GP Γ G (insert v s) :=
  QuotientGroup.lift _ (Coprod.lift (gpIncl (subset_insert' s v)) (amalgRight Γ G s v))
    (Subgroup.normalClosure_le_normal (by
      simp only [retractAmalgamRels, Set.range_subset_iff]
      intro x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, Coprod.lift_apply_inl,
        Coprod.lift_apply_inr, amalgRight, MonoidHom.noncommCoprod_apply, map_one, mul_one,
        gpIncl_gpIncl, mul_inv_cancel]))

theorem amalgToGp_amk (s : Set V) (v : V)
    (y : Coprod (GP Γ G s) (GP Γ G (linkIn Γ s v) × G v)) :
    amalgToGp Γ G s v (amk Γ G s v y) =
      Coprod.lift (gpIncl (subset_insert' s v)) (amalgRight Γ G s v) y :=
  rfl

theorem amalgToGp_gpToAmalg (s : Set V) (v : V) (x : GP Γ G (insert v s)) :
    amalgToGp Γ G s v (gpToAmalg Γ G s v x) = x := by
  have h : (amalgToGp Γ G s v).comp (gpToAmalg Γ G s v) = MonoidHom.id (GP Γ G (insert v s)) := by
    apply gp_ext
    intro u a
    rw [MonoidHom.comp_apply, gpToAmalg, gpLift_of, MonoidHom.id_apply]
    by_cases huv : u = v
    · cases huv
      simp only [toAmalgFam_v, amalgToGp_amk, Coprod.lift_apply_inr, amalgRight,
        MonoidHom.noncommCoprod_apply, map_one, one_mul]
    · by_cases hus : u ∈ s
      · simp only [toAmalgFam_s Γ G s v huv hus, amalgToGp_amk, Coprod.lift_apply_inl,
          gpIncl_of _ hus]
      · have hui : u ∉ insert v s := fun h => (Set.mem_insert_iff.mp h).elim huv hus
        rw [toAmalgFam_out Γ G s v huv hus, map_one, gpOf_killed hui]
  exact DFunLike.congr_fun h x

/-- **Step 6**: adding a vertex is a retract amalgam, so it preserves PBH. -/
theorem gp_insert_pbh (hR : RetractAmalgamClosure) (s : Set V) (v : V)
    (hs : SatisfiesPBH (GP Γ G s)) (hG : SatisfiesPBH (G v)) :
    SatisfiesPBH (GP Γ G (insert v s)) := by
  have hA : SatisfiesPBH (AmalgV Γ G s v) :=
    hR _ _ _ (gpIncl (Γ := Γ) (G := G) (linkIn_subset Γ s v)) (gpRestr (linkIn_subset Γ s v))
      (gpRestr_gpIncl (linkIn_subset Γ s v)) hs hG
  exact hA.of_injective (gpToAmalg Γ G s v)
    (Function.LeftInverse.injective (g := amalgToGp Γ G s v) (amalgToGp_gpToAmalg Γ G s v))

/-- The trivial group satisfies PBH: it acts on a point with an action of type (A). -/
theorem satisfiesPBH_unit : SatisfiesPBH Unit := by
  refine SatisfiesPBH.of_isTypeA (S := Unit) ⟨⟨fun _ => Subsingleton.elim _ _⟩, inferInstance,
    fun s => ?_, inferInstance⟩
  exact (Group.fg_iff_subgroup_fg _).mp inferInstance

theorem gp_empty_pbh : SatisfiesPBH (GP Γ G ∅) := by
  haveI := gp_empty_subsingleton (Γ := Γ) (G := G)
  exact satisfiesPBH_unit.of_injective (1 : GP Γ G ∅ →* Unit) fun a b _ => Subsingleton.elim a b

/-- **BFFHZ Question 3.1 reduces to closure under retract amalgams.** -/
theorem question31_of_retractAmalgamClosure (hR : RetractAmalgamClosure) : Question31 := by
  intro V _ Γ G _ hG
  have key : ∀ s : Finset V, SatisfiesPBH (GP Γ G (s : Set V)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty]
      exact gp_empty_pbh Γ G
    | insert v s hv ih =>
      rw [Finset.coe_insert]
      exact gp_insert_pbh Γ G hR (s : Set V) v ih (hG v)
  haveI := Fintype.ofFinite V
  have hU := key Finset.univ
  rw [Finset.coe_univ] at hU
  exact hU.of_injective (gpUnivEquiv Γ G).toMonoidHom (gpUnivEquiv Γ G).injective

end

end GroupApproximation.BHPalomar.GraphProducts
