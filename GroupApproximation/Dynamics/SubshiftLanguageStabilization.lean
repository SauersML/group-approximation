import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-!
# Language stabilization for decreasing closed families

sec:chain-core, proof of lem:chain-core-models.  The retained subshifts `Z_r` decrease, and "at each
fixed length the decreasing finite languages of `Z_r` stabilize to the language of `Y_0`", where
`Y_0 = ⋂ r, Z_r`; "compactness makes `Y_0` nonempty".  The general-`X` step of the same proof uses the
same stabilization for the decreasing images `ρ_lm(Y_l)`.

Nothing here is symbolic until the last section.  For a decreasing sequence of closed subsets of a
compact space and a continuous map into a finite T₁ space, the images decrease and stabilize, and
their eventual value is the image of the intersection.  The language of a set of configurations
`Z ⊆ ℤ → A` on a finite window `U` is its image under restriction to `U`.

## Main results
* `nonempty_iInter_of_antitone`: a decreasing sequence of nonempty closed sets in a compact space has
  nonempty intersection.
* `image_iInter_eq_iInter_image_of_antitone`: `f '' ⋂ r, Z r = ⋂ r, f '' Z r`.
* `exists_eq_iInter_of_antitone`: a decreasing sequence of subsets of a finite type is eventually
  equal to its intersection.
* `exists_image_eq_image_iInter_of_antitone`: the images stabilize to the image of the intersection.
* `exists_restrict_image_eq_of_antitone`: the symbolic form, languages on a finite window `U`.
* `mem_of_forall_finset_agree`: a configuration all of whose finite windows are realized in a closed
  set of configurations belongs to it.
-/

namespace GroupApproximation.ChainCore

open Set

section Stabilization

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A decreasing sequence of nonempty closed subsets of a compact space has nonempty intersection. -/
theorem nonempty_iInter_of_antitone [CompactSpace X] {Z : ℕ → Set X} (hZ : Antitone Z)
    (hcl : ∀ r, IsClosed (Z r)) (hne : ∀ r, (Z r).Nonempty) : (⋂ r, Z r).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z
    (fun r => hZ (Nat.le_succ r)) hne (hcl 0).isCompact hcl

/-- In a compact space, the continuous image of a decreasing intersection of closed sets is the
intersection of the images, when the points of the target are closed. -/
theorem image_iInter_eq_iInter_image_of_antitone [CompactSpace X] [T1Space Y] {f : X → Y}
    (hf : Continuous f) {Z : ℕ → Set X} (hZ : Antitone Z) (hcl : ∀ r, IsClosed (Z r)) :
    f '' ⋂ r, Z r = ⋂ r, f '' Z r := by
  refine Subset.antisymm (image_iInter_subset Z f) fun y hy => ?_
  rw [mem_iInter] at hy
  have hfy : IsClosed (f ⁻¹' {y}) := isClosed_singleton.preimage hf
  obtain ⟨x, hx⟩ := nonempty_iInter_of_antitone (Z := fun r => Z r ∩ f ⁻¹' {y})
    (fun _ _ hab => inter_subset_inter_left _ (hZ hab)) (fun r => (hcl r).inter hfy)
    (fun r => by
      obtain ⟨x, hx, hxy⟩ := hy r
      exact ⟨x, hx, hxy⟩)
  rw [mem_iInter] at hx
  exact ⟨x, mem_iInter.mpr fun r => (hx r).1, (hx 0).2⟩

omit [TopologicalSpace Y] in
/-- A decreasing sequence of subsets of a finite type is eventually equal to its intersection. -/
theorem exists_eq_iInter_of_antitone [Finite Y] {S : ℕ → Set Y} (hS : Antitone S) :
    ∃ R, ∀ r, R ≤ r → S r = ⋂ r, S r := by
  obtain ⟨R, hR⟩ := Nat.sInf_mem (range_nonempty fun r => (S r).ncard)
  have hR' : (S R).ncard = sInf (range fun r => (S r).ncard) := hR
  have hmin : ∀ r, (S R).ncard ≤ (S r).ncard := fun r => by
    rw [hR']
    exact Nat.sInf_le (mem_range_self r)
  have heq : ∀ r, R ≤ r → S r = S R := fun r hr => eq_of_subset_of_ncard_le (hS hr) (hmin r)
  refine ⟨R, fun r hr => ?_⟩
  rw [heq r hr]
  refine Subset.antisymm (fun y hy => mem_iInter.mpr fun k => ?_) (iInter_subset S R)
  rcases le_total R k with hk | hk
  · rw [heq k hk]
    exact hy
  · exact hS hk hy

/-- The images of a decreasing sequence of closed subsets of a compact space in a finite T₁ space
stabilize, and their eventual value is the image of the intersection. -/
theorem exists_image_eq_image_iInter_of_antitone [CompactSpace X] [T1Space Y] [Finite Y]
    {f : X → Y} (hf : Continuous f) {Z : ℕ → Set X} (hZ : Antitone Z)
    (hcl : ∀ r, IsClosed (Z r)) : ∃ R, ∀ r, R ≤ r → f '' Z r = f '' ⋂ r, Z r := by
  obtain ⟨R, hR⟩ := exists_eq_iInter_of_antitone (S := fun r => f '' Z r)
    (fun _ _ hab _ ⟨x, hx, hxy⟩ => ⟨x, hZ hab hx, hxy⟩)
  refine ⟨R, fun r hr => ?_⟩
  rw [image_iInter_eq_iInter_image_of_antitone hf hZ hcl]
  exact hR r hr

end Stabilization

section Symbolic

variable {A : Type*} [TopologicalSpace A]

/-- sec:chain-core: on each finite window, the decreasing languages of a decreasing sequence of
closed sets of configurations over a finite alphabet stabilize to the language of their
intersection. -/
theorem exists_restrict_image_eq_of_antitone [DiscreteTopology A] [Finite A]
    {Z : ℕ → Set (ℤ → A)} (hZ : Antitone Z) (hcl : ∀ r, IsClosed (Z r)) (U : Finset ℤ) :
    ∃ R, ∀ r, R ≤ r →
      (fun (x : ℤ → A) (i : U) => x i) '' Z r = (fun (x : ℤ → A) (i : U) => x i) '' ⋂ r, Z r :=
  exists_image_eq_image_iInter_of_antitone (f := fun (x : ℤ → A) (i : U) => x i)
    (continuous_pi fun i : U => continuous_apply (i : ℤ)) hZ hcl

/-- A configuration all of whose finite windows are realized in a closed set of configurations
belongs to it. -/
theorem mem_of_forall_finset_agree {Z : Set (ℤ → A)} (hZ : IsClosed Z) {x : ℤ → A}
    (h : ∀ U : Finset ℤ, ∃ y ∈ Z, ∀ i ∈ U, y i = x i) : x ∈ Z := by
  rw [← hZ.closure_eq, mem_closure_iff]
  intro o ho hxo
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp ho x hxo
  obtain ⟨y, hy, hyx⟩ := h I
  refine ⟨y, hIu fun i hi => ?_, hy⟩
  rw [hyx i hi]
  exact (hu i hi).2

end Symbolic

end GroupApproximation.ChainCore
