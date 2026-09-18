import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraPolar
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 2: rigid stabilisers as subgroups, centralisers and conjugates

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-16` (Rubin route).  For a homeomorphism `T` of `X` and `O ⊆ X`,
`rubinRigidSubgroup T O = F_O = {g ∈ [[T]] | SupportedIn g O}` as a subgroup of `[[T]]`; its
underlying set is `rigidStabSet T O` (InfraPolar.lean, lane `sk-flip-06`).

* `rubinConjSubgroup_rubinRigidSubgroup`: `g F_O g⁻¹ = F_{g⁻¹ ⁻¹' O}` (`supportedIn_conj_iff`
  applied to `g⁻¹`).
* `centralizer_rubinRigidSubgroup` (T minimal, `O` open): `C(F_O) = F_{Oᶜ}` (lane 06).
* `rubinRigidSubgroup_interior` (T₂): `F_{interior S} = F_S`.
* `rubinRigidSubgroup_inf_compl_eq_bot`: `F_O ⊓ F_{Oᶜ} = ⊥`.
* `rubinRigid_dichotomy` (T minimal, `O, W` open): `F_O ⊓ F_W ≠ ⊥ ∨ F_W ≤ F_{Oᶜ}`.  If `O ∩ W` is
  nonempty it supports a nontrivial element (`exists_supportedIn_ne_one`); otherwise `W ⊆ Oᶜ`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

section RubinRigid

variable {X : Type*} [TopologicalSpace X]

/-- The rigid stabiliser `F_O = {g ∈ [[T]] | SupportedIn g O}` as a subgroup of `[[T]]`. -/
def rubinRigidSubgroup (T : X ≃ₜ X) (O : Set X) : Subgroup (topologicalFullGroup T) where
  carrier := rigidStabSet T O
  mul_mem' {a b} ha hb := by
    show SupportedIn ((a * b : topologicalFullGroup T) : X ≃ₜ X) O
    intro x hx
    have hbx : (b : X ≃ₜ X) x = x := (mem_rigidStabSet.1 hb) x hx
    have hax : (a : X ≃ₜ X) x = x := (mem_rigidStabSet.1 ha) x hx
    show (a : X ≃ₜ X) ((b : X ≃ₜ X) x) = x
    rw [hbx, hax]
  one_mem' := by
    show SupportedIn ((1 : topologicalFullGroup T) : X ≃ₜ X) O
    intro x _
    rfl
  inv_mem' {a} ha := by
    show SupportedIn ((a⁻¹ : topologicalFullGroup T) : X ≃ₜ X) O
    intro x hx
    have h1 : (a : X ≃ₜ X).symm ((a : X ≃ₜ X) x) = x := (a : X ≃ₜ X).symm_apply_apply x
    rw [(mem_rigidStabSet.1 ha) x hx] at h1
    exact h1

theorem mem_rubinRigidSubgroup {T : X ≃ₜ X} {O : Set X} {g : topologicalFullGroup T} :
    g ∈ rubinRigidSubgroup T O ↔ SupportedIn (g : X ≃ₜ X) O :=
  Iff.rfl

theorem coe_rubinRigidSubgroup (T : X ≃ₜ X) (O : Set X) :
    (rubinRigidSubgroup T O : Set (topologicalFullGroup T)) = rigidStabSet T O :=
  rfl

theorem rubinRigidSubgroup_mono {T : X ≃ₜ X} {O O' : Set X} (h : O ⊆ O') :
    rubinRigidSubgroup T O ≤ rubinRigidSubgroup T O' :=
  fun _ hg => (mem_rubinRigidSubgroup.1 hg).mono h

/-- Conjugating `F_O` by `g` gives `F_{g⁻¹ ⁻¹' O} = F_{g '' O}`. -/
theorem rubinConjSubgroup_rubinRigidSubgroup {T : X ≃ₜ X} (g : topologicalFullGroup T)
    (O : Set X) :
    rubinConjSubgroup g (rubinRigidSubgroup T O) =
      rubinRigidSubgroup T (((g : X ≃ₜ X)⁻¹ : X ≃ₜ X) ⁻¹' O) := by
  ext x
  rw [mem_rubinConjSubgroup, mem_rubinRigidSubgroup, mem_rubinRigidSubgroup]
  have hc : ((g⁻¹ * x * g : topologicalFullGroup T) : X ≃ₜ X) =
      (g : X ≃ₜ X)⁻¹ * (x : X ≃ₜ X) * ((g : X ≃ₜ X)⁻¹)⁻¹ := by
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hc]
  exact supportedIn_conj_iff ((g : X ≃ₜ X)⁻¹) (x : X ≃ₜ X) O

/-- Rigid stabilisers do not see the difference between a set and its interior. -/
theorem rubinRigidSubgroup_interior [T2Space X] {T : X ≃ₜ X} {S : Set X} :
    rubinRigidSubgroup T (interior S) = rubinRigidSubgroup T S :=
  SetLike.coe_injective (rigidStabSet_interior_eq (T := T) (S := S))

/-- `F_O ⊓ F_{Oᶜ} = ⊥`. -/
theorem rubinRigidSubgroup_inf_compl_eq_bot (T : X ≃ₜ X) (O : Set X) :
    rubinRigidSubgroup T O ⊓ rubinRigidSubgroup T Oᶜ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have h1 : SupportedIn (g : X ≃ₜ X) O := (Subgroup.mem_inf.1 hg).1
  have h2 : SupportedIn (g : X ≃ₜ X) Oᶜ := (Subgroup.mem_inf.1 hg).2
  refine Subtype.ext (Homeomorph.ext fun x => ?_)
  show (g : X ≃ₜ X) x = x
  by_cases hx : x ∈ O
  · exact h2 x (Set.notMem_compl_iff.2 hx)
  · exact h1 x hx

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]

/-- For open `O`, `C(F_O) = F_{Oᶜ}` as subgroups of `[[T]]`. -/
theorem centralizer_rubinRigidSubgroup {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O : Set X}
    (hO : IsOpen O) :
    Subgroup.centralizer (rubinRigidSubgroup T O : Set (topologicalFullGroup T)) =
      rubinRigidSubgroup T Oᶜ :=
  SetLike.coe_injective (coe_centralizer_rigidStabSet_of_isOpen hT hO)

/-- For open `O, W`: either `F_O ⊓ F_W ≠ ⊥`, or `F_W ≤ F_{Oᶜ}`. -/
theorem rubinRigid_dichotomy {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O W : Set X} (hO : IsOpen O)
    (hW : IsOpen W) :
    rubinRigidSubgroup T O ⊓ rubinRigidSubgroup T W ≠ ⊥ ∨
      rubinRigidSubgroup T W ≤ rubinRigidSubgroup T Oᶜ := by
  by_cases hne : (O ∩ W).Nonempty
  · left
    intro hbot
    obtain ⟨σ, hσ, hσOW, x, hx⟩ := exists_supportedIn_ne_one hT (hO.inter hW) hne
    have hmem : (⟨σ, hσ⟩ : topologicalFullGroup T) ∈
        rubinRigidSubgroup T O ⊓ rubinRigidSubgroup T W :=
      Subgroup.mem_inf.2 ⟨hσOW.mono Set.inter_subset_left, hσOW.mono Set.inter_subset_right⟩
    have h1 : (⟨σ, hσ⟩ : topologicalFullGroup T) = 1 :=
      (Subgroup.eq_bot_iff_forall _).1 hbot _ hmem
    have h2 : σ = 1 := congrArg Subtype.val h1
    rw [h2] at hx
    exact hx rfl
  · right
    exact rubinRigidSubgroup_mono (fun x hxW => Set.mem_compl fun hxO => hne ⟨x, hxO, hxW⟩)

end RubinRigid

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.coe_rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_mono
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinConjSubgroup_rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_interior
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_inf_compl_eq_bot
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigid_dichotomy
