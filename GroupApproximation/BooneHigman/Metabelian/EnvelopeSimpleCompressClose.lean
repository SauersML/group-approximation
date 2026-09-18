import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleCompressShrink
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleDisplaceClauses
import GroupApproximation.Meta.AxiomGuard

/-!
# Clause (C): `⁅V_X(H), V_X(H)⁆` compresses sets missing a cone into any cone

Proves `RNCompressStatement` (`rnCompressStatement_holds`).

Route.  Invariance of `MissesCone` is `missesCone_image_rn`.  For compression, let `S` miss
`cone c` and fix a target `cone w`.  Extend `c` and `w` to nonempty words `c'`, `w'` with
disjoint cones (`exists_disjoint_extensions`).  By `exists_commutator_compress_cone` there are
`k₁, k₂ ∈ ⁅V_X, V_X⁆` with `k₁` carrying `(cone c')ᶜ ⊇ S` into `cone c'` and `k₂` carrying
`(cone w')ᶜ ⊇ cone c'` into `cone w' ⊆ cone w`; then `k₂ * k₁` works, and it lies in
`⁅V_X(H), V_X(H)⁆` by `Subgroup.commutator_mono` and `higmanThompsonV_le_rn`.
Self-similarity of `H` is not used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

variable {X : Type*}

theorem exists_disjoint_extensions [Nontrivial X] (c w : List X) :
    ∃ c' w' : List X, c <+: c' ∧ w <+: w' ∧ c' ≠ [] ∧ w' ≠ [] ∧
      Disjoint (cone c') (cone w') := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  by_cases hcw : c <+: w
  · exact ⟨w ++ [x], w ++ [y], hcw.trans (List.prefix_append w [x]),
      List.prefix_append w [y], List.append_ne_nil_of_right_ne_nil w (List.cons_ne_nil x []),
      List.append_ne_nil_of_right_ne_nil w (List.cons_ne_nil y []),
      disjoint_cone (not_prefix_append_of_ne hxy w [] [])
        (not_prefix_append_of_ne hxy.symm w [] [])⟩
  · by_cases hwc : w <+: c
    · exact ⟨c ++ [x], c ++ [y], List.prefix_append c [x],
        hwc.trans (List.prefix_append c [y]),
        List.append_ne_nil_of_right_ne_nil c (List.cons_ne_nil x []),
        List.append_ne_nil_of_right_ne_nil c (List.cons_ne_nil y []),
        disjoint_cone (not_prefix_append_of_ne hxy c [] [])
          (not_prefix_append_of_ne hxy.symm c [] [])⟩
    · have hc : c ≠ [] := fun e => hcw (by rw [e]; exact List.nil_prefix)
      have hw : w ≠ [] := fun e => hwc (by rw [e]; exact List.nil_prefix)
      exact ⟨c, w, List.prefix_refl c, List.prefix_refl w, hc, hw, disjoint_cone hcw hwc⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_disjoint_extensions

/-- **Compression**: a commutator of `V_X(H)` carries a set missing a cone into `cone w`. -/
theorem exists_commutator_image_subset_cone [Finite X] [Nontrivial X]
    (H : Subgroup (TreeAut X)) (w : List X) {S : Set (Cantor X)} (hS : MissesCone S) :
    ∃ k ∈ ⁅roverNekrashevych X H, roverNekrashevych X H⁆, k '' S ⊆ cone w := by
  obtain ⟨c, hc⟩ := hS
  obtain ⟨c', w', hcc, hww, hc'0, hw'0, hdis⟩ := exists_disjoint_extensions c w
  obtain ⟨k₁, hk₁, hk₁p⟩ := exists_commutator_compress_cone hc'0
  obtain ⟨k₂, hk₂, hk₂p⟩ := exists_commutator_compress_cone hw'0
  have hle := Subgroup.commutator_mono (higmanThompsonV_le_rn H) (higmanThompsonV_le_rn H)
  refine ⟨k₂ * k₁, hle (mul_mem hk₂ hk₁), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs1 : s ∉ cone c' := fun h => Set.disjoint_left.mp hc hs (cone_subset_of_prefix hcc h)
  have hs2 : k₁ s ∉ cone w' := fun h => Set.disjoint_left.mp hdis (hk₁p s hs1) h
  exact cone_subset_of_prefix hww (hk₂p (k₁ s) hs2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_commutator_image_subset_cone

theorem compressible_rn [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)) (w : List X) :
    Compressible (roverNekrashevych X H) (cone w) MissesCone :=
  ⟨fun _ hS _ hf => missesCone_image_rn H hS hf,
    fun _ hS => exists_commutator_image_subset_cone H w hS⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.compressible_rn

/-- **Clause (C)** of `RNDisplaceCompressStatement`. -/
theorem rnCompressStatement_holds : RNCompressStatement := by
  intro X _ _ H _ u a
  exact compressible_rn H (u ++ [a, a])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCompressStatement_holds

end GroupApproximation.BooneHigman.Metabelian.Envelope
