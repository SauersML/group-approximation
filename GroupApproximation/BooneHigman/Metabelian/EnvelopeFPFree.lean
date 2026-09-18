import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import GroupApproximation.BooneHigman.V.Supports
import GroupApproximation.BooneHigman.V.Transitive
import Mathlib.GroupTheory.Coprod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The free product `V_X ∗ (H ∗ H)` maps onto the Röver–Nekrashevych group

The finite presentation of `V_X(H)` is a presentation on the generators of `V_X` and of `H`.
This module builds the free product `RNFree X H = V_X ∗ (H ∗ H)` and the homomorphism
`rnFreeHom H x₀ : RNFree X H →* V_X(H)` sending `V_X` identically, the first copy of `H` to
`h ↦ h` acting on the whole Cantor set and the second copy to `h ↦ localize [x₀] h`, acting in
the cone of the one-letter word `[x₀]`.

Route.
* `rnFreeToPerm_mem`: the image lies in `V_X(H)`, by induction on the free product.
* `rnGenerators_subset_range`: every generator of `V_X(H)` is in the image.  `V_X` and the
  elements localised at the empty word are images of generators.  For a nonempty word `w`,
  `exists_mapsCone_of_ne_nil` gives `g ∈ V_X` carrying `cone [x₀]` onto `cone w`, and
  `MapsCone.conj_localize` gives `g * localize [x₀] h * g⁻¹ = localize w h`.
* `rnFreeHom_surjective`: hence the corestriction is surjective.
* `closure_rnFreeGenerators`: the three factor images generate `RNFree X H`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

variable (X) in
/-- The free product `V_X ∗ (H ∗ H)`. -/
abbrev RNFree (H : Subgroup (TreeAut X)) :=
  Monoid.Coprod ↥(higmanThompsonV X) (Monoid.Coprod ↥H ↥H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFree

/-- `V_X ∗ (H ∗ H) → Sym(Cantor X)`: inclusion on `V_X`, `h ↦ h` on the first copy of `H` and
`h ↦ localize [x₀] h` on the second. -/
def rnFreeToPerm (H : Subgroup (TreeAut X)) (x₀ : X) : RNFree X H →* Equiv.Perm (Cantor X) :=
  Monoid.Coprod.lift (higmanThompsonV X).subtype
    (Monoid.Coprod.lift (cantorHom.comp H.subtype)
      ((localize [x₀]).comp (cantorHom.comp H.subtype)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeToPerm

theorem rnFreeToPerm_inl (H : Subgroup (TreeAut X)) (x₀ : X) (v : ↥(higmanThompsonV X)) :
    rnFreeToPerm H x₀ (Monoid.Coprod.inl v) = (v : Equiv.Perm (Cantor X)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeToPerm_inl

theorem rnFreeToPerm_inr_inl (H : Subgroup (TreeAut X)) (x₀ : X) (h : ↥H) :
    rnFreeToPerm H x₀ (Monoid.Coprod.inr (Monoid.Coprod.inl h)) = cantorHom (h : TreeAut X) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeToPerm_inr_inl

theorem rnFreeToPerm_inr_inr (H : Subgroup (TreeAut X)) (x₀ : X) (h : ↥H) :
    rnFreeToPerm H x₀ (Monoid.Coprod.inr (Monoid.Coprod.inr h)) =
      localize [x₀] (cantorHom (h : TreeAut X)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeToPerm_inr_inr

theorem rnFreeToPerm_mem (H : Subgroup (TreeAut X)) (x₀ : X) (k : RNFree X H) :
    rnFreeToPerm H x₀ k ∈ roverNekrashevych X H := by
  induction k using Monoid.Coprod.induction_on with
  | inl v =>
    rw [rnFreeToPerm_inl]
    exact higmanThompsonV_le_rn H v.2
  | inr n =>
    induction n using Monoid.Coprod.induction_on with
    | inl h =>
      rw [rnFreeToPerm_inr_inl]
      exact cantorHom_mem_roverNekrashevych H h.2
    | inr h =>
      rw [rnFreeToPerm_inr_inr]
      exact localize_mem_roverNekrashevych H [x₀] h.2
    | mul y z hy hz =>
      rw [map_mul, map_mul]
      exact (roverNekrashevych X H).mul_mem hy hz
  | mul y z hy hz =>
    rw [map_mul]
    exact (roverNekrashevych X H).mul_mem hy hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeToPerm_mem

/-- The presentation map `V_X ∗ (H ∗ H) →* V_X(H)`. -/
def rnFreeHom (H : Subgroup (TreeAut X)) (x₀ : X) : RNFree X H →* ↥(roverNekrashevych X H) :=
  (rnFreeToPerm H x₀).codRestrict (roverNekrashevych X H) (rnFreeToPerm_mem H x₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeHom

theorem rnGenerators_subset_range [Nontrivial X] (H : Subgroup (TreeAut X)) (x₀ : X) :
    rnGenerators H ⊆ (rnFreeToPerm H x₀).range := by
  rintro f (hf | ⟨w, h, hh, rfl⟩)
  · exact MonoidHom.mem_range.mpr ⟨Monoid.Coprod.inl ⟨f, hf⟩, rfl⟩
  · by_cases hw : w = []
    · subst hw
      rw [localize_nil]
      refine MonoidHom.mem_range.mpr ⟨Monoid.Coprod.inr (Monoid.Coprod.inl ⟨h, hh⟩), ?_⟩
      exact rnFreeToPerm_inr_inl H x₀ ⟨h, hh⟩
    · obtain ⟨g, hg, hmap⟩ := exists_mapsCone_of_ne_nil (List.cons_ne_nil x₀ []) hw
      refine MonoidHom.mem_range.mpr ⟨Monoid.Coprod.inl ⟨g, hg⟩ *
        Monoid.Coprod.inr (Monoid.Coprod.inr ⟨h, hh⟩) * (Monoid.Coprod.inl ⟨g, hg⟩)⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, rnFreeToPerm_inl, rnFreeToPerm_inr_inr]
      exact hmap.conj_localize (cantorHom h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnGenerators_subset_range

theorem roverNekrashevych_le_range [Nontrivial X] (H : Subgroup (TreeAut X)) (x₀ : X) :
    roverNekrashevych X H ≤ (rnFreeToPerm H x₀).range :=
  (Subgroup.closure_le _).mpr (rnGenerators_subset_range H x₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.roverNekrashevych_le_range

theorem rnFreeHom_surjective [Nontrivial X] (H : Subgroup (TreeAut X)) (x₀ : X) :
    Function.Surjective (rnFreeHom H x₀) := by
  intro v
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (roverNekrashevych_le_range H x₀ v.2)
  exact ⟨k, Subtype.ext hk⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeHom_surjective

/-- The images of the three factors of `V_X ∗ (H ∗ H)`. -/
def rnFreeGenerators (H : Subgroup (TreeAut X)) : Set (RNFree X H) :=
  (Set.range fun v : ↥(higmanThompsonV X) => (Monoid.Coprod.inl v : RNFree X H)) ∪
    (Set.range fun h : ↥H => (Monoid.Coprod.inr (Monoid.Coprod.inl h) : RNFree X H)) ∪
    Set.range fun h : ↥H => (Monoid.Coprod.inr (Monoid.Coprod.inr h) : RNFree X H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeGenerators

theorem closure_rnFreeGenerators (H : Subgroup (TreeAut X)) :
    Subgroup.closure (rnFreeGenerators H) = ⊤ := by
  have hinr : ∀ n : Monoid.Coprod ↥H ↥H,
      (Monoid.Coprod.inr n : RNFree X H) ∈ Subgroup.closure (rnFreeGenerators H) := by
    intro n
    induction n using Monoid.Coprod.induction_on with
    | inl h =>
      exact Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_right _ ⟨h, rfl⟩))
    | inr h => exact Subgroup.subset_closure (Set.mem_union_right _ ⟨h, rfl⟩)
    | mul y z hy hz =>
      rw [map_mul]
      exact (Subgroup.closure (rnFreeGenerators H)).mul_mem hy hz
  rw [Subgroup.eq_top_iff']
  intro k
  induction k using Monoid.Coprod.induction_on with
  | inl v => exact Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_union_left _ ⟨v, rfl⟩))
  | inr n => exact hinr n
  | mul y z hy hz => exact (Subgroup.closure (rnFreeGenerators H)).mul_mem hy hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.closure_rnFreeGenerators

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
