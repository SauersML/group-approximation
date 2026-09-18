import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# Parking: elements fixing a cone are products of fragments

`frag_park`: if `e ∈ V_X(H)` fixes `cone u` pointwise (`4 ≤ |u|`), then `e` lies in the closure
of `fragPieces H`.

Route.  Let `σ` be the swap family of `frag_swap_family` over all words `w ≠ u` of length `|u|`.
Then `σ x = u x` for `x ∉ cone u`, `σ (u x) = x` for `x ∉ cone u`, and `σ` fixes `cone (u ++ u)`.
Pointwise, `localize u e * σ = σ * e`, so `e = σ⁻¹ * localize u e * σ`, where `localize u e` is a
piece (supported in `cone u`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees
open HydeLodha

noncomputable section

variable {X : Type*} [Finite X]

theorem frag_park_of_family (H : Subgroup (TreeAut X)) {u : List X} (hu : 4 ≤ u.length)
    (T : Finset (List X)) (hT : ∀ w, w ∈ T ↔ w.length = u.length ∧ w ≠ u)
    {e : Equiv.Perm (Cantor X)} (he : e ∈ roverNekrashevych X H)
    (hfix : ∀ y, e (prepend u y) = prepend u y) : e ∈ Subgroup.closure (fragPieces H) := by
  obtain ⟨k, hk, h1, h2, h3⟩ := frag_swap_family H hu T fun w hw => (hT w).mp hw
  have hfw : ∀ x, x ∉ cone u → firstWord u.length x ∈ T := by
    intro x hx
    refine (hT _).mpr ⟨length_firstWord _ x, fun h => hx ?_⟩
    have h' := isStreamPrefix_firstWord u.length x
    rw [h] at h'
    exact h'
  have S1 : ∀ x, x ∉ cone u → k x = prepend u x := by
    intro x hx
    have e1 := h1 _ (hfw x hx) (dropN u.length x)
    rw [prepend_append, prepend_firstWord] at e1
    exact e1
  have S2 : ∀ x, x ∉ cone u → k (prepend u x) = x := by
    intro x hx
    have e2 := h2 _ (hfw x hx) (dropN u.length x)
    rw [prepend_append, prepend_firstWord] at e2
    exact e2
  have S3 : ∀ y, k (prepend u (prepend u y)) = prepend u (prepend u y) := by
    intro y
    refine h3 _ fun w hw => ?_
    obtain ⟨hwl, hwu⟩ := (hT w).mp hw
    rw [← prepend_append]
    have hz : prepend (u ++ u) y ∈ cone (u ++ u) := prepend_mem_cone _ y
    exact ⟨fun h => Set.disjoint_left.mp (disjoint_cone_of_length_eq hwl hwu) h
        (cone_append_subset u u hz),
      Set.disjoint_left.mp (disjoint_cone_of_length_eq (by simp only [List.length_append, hwl])
        (fun h => hwu (List.append_cancel_left h).symm)) hz⟩
  have key : localize u e * k = k * e := by
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hx : x ∈ cone u
    · obtain ⟨x', rfl⟩ := mem_cone_iff.mp hx
      rw [hfix]
      by_cases hx' : x' ∈ cone u
      · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hx'
        rw [S3, localize_apply_prepend, hfix]
      · rw [S2 x' hx', localize_apply_of_not (w := u) (x := x') hx' e]
    · have hex : e x ∉ cone u := by
        intro h
        obtain ⟨y, hy⟩ := mem_cone_iff.mp h
        apply hx
        have hxy : x = prepend u y := e.injective (hy.trans (hfix y).symm)
        rw [hxy]
        exact prepend_mem_cone u y
      rw [S1 x hx, localize_apply_prepend, S1 (e x) hex]
  have hloc : localize u e ∈ Subgroup.closure (fragPieces H) :=
    Subgroup.subset_closure (fragPieces_of_long (frag_localize_mem H u he) hu hu
      ((localize_supportedIn u e).mono Set.subset_union_left))
  have heq : e = k⁻¹ * localize u e * k := by
    rw [mul_assoc, key, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [heq]
  exact (Subgroup.closure (fragPieces H)).mul_mem
    ((Subgroup.closure (fragPieces H)).mul_mem ((Subgroup.closure (fragPieces H)).inv_mem hk)
      hloc) hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_park_of_family

theorem frag_words_finset (u : List X) :
    ∃ T : Finset (List X), ∀ w, w ∈ T ↔ w.length = u.length ∧ w ≠ u := by
  classical
  refine ⟨(finite_words_length_eq (X := X) u.length).toFinset.erase u, fun w => ?_⟩
  rw [Finset.mem_erase, Set.Finite.mem_toFinset]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_words_finset

/-- **Parking.** -/
theorem frag_park (H : Subgroup (TreeAut X)) {u : List X} (hu : 4 ≤ u.length)
    {e : Equiv.Perm (Cantor X)} (he : e ∈ roverNekrashevych X H)
    (hfix : ∀ y, e (prepend u y) = prepend u y) : e ∈ Subgroup.closure (fragPieces H) := by
  obtain ⟨T, hT⟩ := frag_words_finset u
  exact frag_park_of_family H hu T hT he hfix

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_park

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
