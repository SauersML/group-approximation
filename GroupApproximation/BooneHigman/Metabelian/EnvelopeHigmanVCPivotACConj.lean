import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotACRefine
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating a deep antichain subgroup by a word (lane bh-met-77s)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`.  Let `g` be a word with the push property at
threshold `N` (`HigmanVCCommonPush d g N`, which always holds for some `N` by
`higmanVCCommon_push`).  Let `C` be an antichain all of whose words have length `≥ B + N`.

`higmanVCPivotAC_push d B g C` is the image antichain: the words `x'` with `g` carrying the cone of
some `x ∈ C` onto the cone of `x'` and `B ≤ |x'|`.  Then:
* it is an antichain (`higmanVCPivotAC_push_isAC`);
* all its words have length `≥ B` (`higmanVCPivotAC_push_length`);
* `mk g * H_C * (mk g)⁻¹ ≤ H_{push}` (`higmanVCPivotAC_conj_mem`).

Only letters with two distinct entries of `C` matter, since the diagonal letters are trivial.  Such
entries are incomparable, and the push property applies to them.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A chosen cone image of `x` under `f` (meaningful when `f` maps the cone of `x` to a cone). -/
noncomputable def higmanVCPivotAC_img {d : ℕ} (f : Equiv.Perm (Cantor (Fin d)))
    (x : List (Fin d)) : List (Fin d) :=
  Classical.epsilon fun x' => MapsCone f x x'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_img

theorem higmanVCPivotAC_img_eq {d : ℕ} (hd : 1 < d) {f : Equiv.Perm (Cantor (Fin d))}
    {x x' : List (Fin d)} (h : MapsCone f x x') : higmanVCPivotAC_img f x = x' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hs : MapsCone f x (higmanVCPivotAC_img f x) :=
    Classical.epsilon_spec (p := fun x' => MapsCone f x x') ⟨x', h⟩
  exact hs.unique h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_img_eq

open Classical in
/-- The pushed antichain: images of the words of `C` whose cone image has length `≥ B`. -/
noncomputable def higmanVCPivotAC_push (d B : ℕ) (g : FreeGroup (List (Fin d) × List (Fin d)))
    (C : Finset (List (Fin d))) : Finset (List (Fin d)) :=
  (C.filter fun x => ∃ x', MapsCone (higmanVCCommon_perm d g) x x' ∧ B ≤ x'.length).image
    (higmanVCPivotAC_img (higmanVCCommon_perm d g))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_push

theorem higmanVCPivotAC_mem_push {d B : ℕ} {g : FreeGroup (List (Fin d) × List (Fin d))}
    {C : Finset (List (Fin d))} {z : List (Fin d)} :
    z ∈ higmanVCPivotAC_push d B g C ↔ ∃ x ∈ C,
      (∃ x', MapsCone (higmanVCCommon_perm d g) x x' ∧ B ≤ x'.length) ∧
        higmanVCPivotAC_img (higmanVCCommon_perm d g) x = z := by
  rw [higmanVCPivotAC_push, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    exact ⟨x, hx.1, hx.2, rfl⟩
  · rintro ⟨x, hx, hP, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hP⟩, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_mem_push

theorem higmanVCPivotAC_push_length {d B : ℕ} (hd : 1 < d)
    {g : FreeGroup (List (Fin d) × List (Fin d))} {C : Finset (List (Fin d))} {z : List (Fin d)}
    (hz : z ∈ higmanVCPivotAC_push d B g C) : B ≤ z.length := by
  obtain ⟨x, _, ⟨x', hx', hB⟩, rfl⟩ := higmanVCPivotAC_mem_push.mp hz
  rw [higmanVCPivotAC_img_eq hd hx']
  exact hB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_push_length

/-- The pushed set of an antichain is an antichain. -/
theorem higmanVCPivotAC_push_isAC {d B : ℕ} (hd : 1 < d)
    (g : FreeGroup (List (Fin d) × List (Fin d))) {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCPivotAC_push d B g C) := by
  intro u hu v hv huv hpre
  obtain ⟨x, hx, ⟨x', hx', _⟩, rfl⟩ := higmanVCPivotAC_mem_push.mp hu
  obtain ⟨y, hy, ⟨y', hy', _⟩, rfl⟩ := higmanVCPivotAC_mem_push.mp hv
  by_cases hxy : x = y
  · subst hxy
    exact huv rfl
  · rw [higmanVCPivotAC_img_eq hd hx', higmanVCPivotAC_img_eq hd hy'] at hpre
    exact higmanVCCommon_incomp_image (by omega) hx' hy' (hC x hx y hy hxy)
      (hC y hy x hx (Ne.symm hxy)) hpre

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_push_isAC

end GroupApproximation.BooneHigman.Metabelian.Envelope
