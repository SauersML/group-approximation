import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonCentral
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# All-swaps presentation: balanced letters and the uniform antichain (lane bh-met-77h)

`higmanVCCentral_words d M` is the finite set of words of length `M` over `Fin d`.  Its members
all have the same length, so it is an antichain (`higmanVCCentral_words_antichain`).

A letter `(u, v)` is *balanced* when `|u| = |v|`.  Let `M ≥ |u|`.  Modulo the standard relators,
a balanced letter is a word in the letters of `higmanVCCentral_words d M`
(`higmanVCCentral_letter_mem`):

* if `u`, `v` are incomparable, split it `M - |u|` times (`higmanVCCommon_mk_deep`), and every
  component of the split has length `M`;
* otherwise it is trivial.

Products of balanced letters follow (`higmanVCCentral_list_mem`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The words of length `M` over `Fin d`. -/
def higmanVCCentral_words (d : ℕ) : ℕ → Finset (List (Fin d))
  | 0 => {[]}
  | M + 1 => Finset.univ.biUnion fun a : Fin d => (higmanVCCentral_words d M).image (List.cons a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_words

theorem higmanVCCentral_words_zero (d : ℕ) : higmanVCCentral_words d 0 = {[]} :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_words_zero

theorem higmanVCCentral_words_succ (d M : ℕ) :
    higmanVCCentral_words d (M + 1) =
      Finset.univ.biUnion fun a : Fin d => (higmanVCCentral_words d M).image (List.cons a) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_words_succ

/-- Membership in `higmanVCCentral_words d M` is having length `M`. -/
theorem higmanVCCentral_mem_words_iff (d : ℕ) :
    ∀ (M : ℕ) (w : List (Fin d)), w ∈ higmanVCCentral_words d M ↔ w.length = M := by
  intro M
  induction M with
  | zero =>
    intro w
    rw [higmanVCCentral_words_zero, Finset.mem_singleton]
    constructor
    · rintro rfl
      rfl
    · intro h
      cases w with
      | nil => rfl
      | cons a t => exact absurd h (by rw [List.length_cons]; omega)
  | succ M ih =>
    intro w
    rw [higmanVCCentral_words_succ, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, _, hw⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      rw [List.length_cons, (ih t).mp ht]
    · intro h
      cases w with
      | nil => exact absurd h (by rw [List.length_nil]; omega)
      | cons a t =>
        refine ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨t, (ih t).mpr ?_, rfl⟩⟩
        rw [List.length_cons] at h
        omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_mem_words_iff

theorem higmanVCCentral_mem_words {d M : ℕ} {w : List (Fin d)} (h : w.length = M) :
    w ∈ higmanVCCentral_words d M :=
  (higmanVCCentral_mem_words_iff d M w).mpr h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_mem_words

/-- The words of length `M` form an antichain. -/
theorem higmanVCCentral_words_antichain (d M : ℕ) :
    ∀ u ∈ higmanVCCentral_words d M, ∀ v ∈ higmanVCCentral_words d M, u ≠ v → ¬ u <+: v :=
  fun u hu v hv hne h => hne (h.eq_of_length
    (((higmanVCCentral_mem_words_iff d M u).mp hu).trans
      ((higmanVCCentral_mem_words_iff d M v).mp hv).symm))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_words_antichain

/-- An `m`-fold split whose components have length `M` is a word in the letters of
`higmanVCCentral_words d M`. -/
theorem higmanVCCentral_deep_mem {d M : ℕ} (m : ℕ) :
    ∀ {x y : List (Fin d)}, x.length + m = M → y.length + m = M →
      higmanVCCommon_deep d m x y ∈ (higmanVCAll_iota (higmanVCCentral_words d M)).range := by
  induction m with
  | zero =>
    intro x y hx hy
    rw [higmanVCCommon_deep_zero]
    exact MonoidHom.mem_range.mpr
      ⟨FreeGroup.of (⟨x, higmanVCCentral_mem_words (by omega)⟩,
        ⟨y, higmanVCCentral_mem_words (by omega)⟩), higmanVCAll_iota_of _ _⟩
  | succ m ih =>
    intro x y hx hy
    rw [higmanVCCommon_deep_succ]
    refine list_prod_mem fun t ht => ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    exact ih (x := x ++ [a]) (y := y ++ [a])
      (by rw [List.length_append, List.length_singleton]; omega)
      (by rw [List.length_append, List.length_singleton]; omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_deep_mem

/-- **Balanced letters.**  Modulo the relators, a letter `(u, v)` with `|u| = |v| ≤ M` is a word
in the letters of `higmanVCCentral_words d M`. -/
theorem higmanVCCentral_letter_mem {d M : ℕ} {u v : List (Fin d)} (huv : u.length = v.length)
    (hM : u.length ≤ M) :
    higmanVCCommon_mk d (FreeGroup.of (u, v)) ∈
      ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M))).range := by
  by_cases h : ¬ u <+: v ∧ ¬ v <+: u
  · rw [← higmanVCCommon_mk_deep (M - u.length) h.1 h.2]
    obtain ⟨r', hr'⟩ := MonoidHom.mem_range.mp
      (higmanVCCentral_deep_mem (M := M) (M - u.length) (x := u) (y := v) (by omega) (by omega))
    exact MonoidHom.mem_range.mpr ⟨r', by rw [MonoidHom.comp_apply, hr']⟩
  · rw [higmanVCCommon_mk_comparable h]
    exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_letter_mem

/-- **Products of balanced letters.** -/
theorem higmanVCCentral_list_mem {d M : ℕ} (L : List (List (Fin d) × List (Fin d)))
    (hL : ∀ p ∈ L, p.1.length = p.2.length ∧ p.1.length ≤ M) :
    higmanVCCommon_mk d (L.map FreeGroup.of).prod ∈
      ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M))).range := by
  rw [map_list_prod]
  refine list_prod_mem fun t ht => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, v⟩ := p
  exact higmanVCCentral_letter_mem (hL _ hp).1 (hL _ hp).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_list_mem

/-- Every finite list of pairs has a common bound on the first lengths. -/
theorem higmanVCCentral_exists_bound {d : ℕ} (L : List (List (Fin d) × List (Fin d))) :
    ∃ M, ∀ p ∈ L, p.1.length ≤ M := by
  induction L with
  | nil => exact ⟨0, fun p hp => absurd hp List.not_mem_nil⟩
  | cons q L ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max q.1.length M, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact le_max_left _ _
    · exact le_trans (hM p hp') (le_max_right _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_exists_bound

end GroupApproximation.BooneHigman.Metabelian.Envelope
