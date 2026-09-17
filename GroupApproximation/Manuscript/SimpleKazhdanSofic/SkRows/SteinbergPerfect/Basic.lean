import GroupApproximation.Steinberg.Perfect
import GroupApproximation.Leavitt.ElementaryPerfect
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg and elementary groups over an index type of size at least three are perfect

Lane `sk-rows-10` (ring-generic Steinberg infrastructure on Khanh's route to the rank-four
`K₂` gap behind tex 733).  No single tex sentence is formalized here; this module supplies the
perfectness input used by the padded-kill step (lane `sk-rows-16`).

## Statement

For every associative unital ring `R` and every finite index type `I` with `3 ≤ |I|`,
`commutator (St_I(R)) = ⊤` and `commutator (EL_I(R)) = ⊤`.

## Route

* `exists_ne_and_ne_of_three_le_card`: for `3 ≤ |I|` and any `i j : I`, the finset
  `(univ.erase i).erase j` has at least `|I| - 2 ≥ 1` elements, so a third index exists.
* Steinberg relation `x_ij(a) = ⁅x_ik(a), x_kj(1)⁆` for `k ∉ {i, j}`
  (`SteinbergGroup.x_commutator`): every generator is a commutator, and the generators
  generate the presented group.  This is the existing corpus lemma
  `SteinbergGroup.isPerfect_of_exists_third` (`Steinberg/Perfect.lean`), specialised here
  through the cardinality hypothesis.
* `EL_I(R)` is the image of `St_I(R)` under the surjection `SteinbergGroup.projection`
  (`SteinbergGroup.projection_surjective`), and images of perfect groups are perfect
  (`commutator_eq_top_of_surjective`, `Leavitt/ElementaryPerfect.lean`).

Nothing is assumed: no `Statement` hypotheses.  `SteinbergPerfectStatement` below is only a
packaged form of the proved theorem, for downstream lanes to cite.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect

/-- If a finite type has at least three elements, any two of its elements admit a third
element distinct from both. -/
theorem exists_ne_and_ne_of_three_le_card {I : Type*} [Fintype I] [DecidableEq I]
    (h : 3 ≤ Fintype.card I) (i j : I) : ∃ k : I, k ≠ i ∧ k ≠ j := by
  have h1 : ((Finset.univ : Finset I).erase i).card = Fintype.card I - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have h2 : ((Finset.univ : Finset I).erase i).card - 1 ≤
      (((Finset.univ : Finset I).erase i).erase j).card :=
    Finset.pred_card_le_card_erase
  have hpos : 0 < (((Finset.univ : Finset I).erase i).erase j).card := by
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, Finset.mem_erase] at hk
  exact ⟨k, hk.2.1, hk.1⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.exists_ne_and_ne_of_three_le_card

/-- **Steinberg groups are perfect in rank at least three.**  For every ring `R` and every
finite index type `I` with `3 ≤ |I|`, the Steinberg group `St_I(R)` equals its commutator
subgroup. -/
theorem steinberg_commutator_eq_top (I R : Type*) [Fintype I] [DecidableEq I] [Ring R]
    (h : 3 ≤ Fintype.card I) : commutator (SteinbergGroup I R) = ⊤ :=
  Group.isPerfect_def.mp
    (SteinbergGroup.isPerfect_of_exists_third (I := I) (R := R)
      fun i j _ ↦ exists_ne_and_ne_of_three_le_card h i j)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.steinberg_commutator_eq_top

/-- `St_I(R)` is a perfect group (`Group.IsPerfect` form) when `3 ≤ |I|`. -/
theorem steinberg_isPerfect (I R : Type*) [Fintype I] [DecidableEq I] [Ring R]
    (h : 3 ≤ Fintype.card I) : Group.IsPerfect (SteinbergGroup I R) :=
  Group.isPerfect_def.mpr (steinberg_commutator_eq_top I R h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.steinberg_isPerfect

/-- **Elementary groups are perfect in rank at least three.**  For every ring `R` and every
finite index type `I` with `3 ≤ |I|`, `EL_I(R)` equals its commutator subgroup.  Proof: push
`steinberg_commutator_eq_top` along the surjection `St_I(R) → EL_I(R)`. -/
theorem elementary_commutator_eq_top (I R : Type*) [Fintype I] [DecidableEq I] [Ring R]
    (h : 3 ≤ Fintype.card I) : commutator (elementaryGroup I R) = ⊤ :=
  GroupApproximation.commutator_eq_top_of_surjective
    (SteinbergGroup.projection (I := I) (R := R))
    SteinbergGroup.projection_surjective
    (steinberg_commutator_eq_top I R h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.elementary_commutator_eq_top

/-- `EL_I(R)` is a perfect group (`Group.IsPerfect` form) when `3 ≤ |I|`. -/
theorem elementaryGroup_isPerfect (I R : Type*) [Fintype I] [DecidableEq I] [Ring R]
    (h : 3 ≤ Fintype.card I) : Group.IsPerfect (elementaryGroup I R) :=
  Group.isPerfect_def.mpr (elementary_commutator_eq_top I R h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.elementaryGroup_isPerfect

/-- The packaged interface for downstream lanes (e.g. `sk-rows-16`): Steinberg groups over
index types of size at least three are perfect, at universes `u` (indices) and `v` (rings).
It is proved outright by `steinbergPerfectStatement`. -/
def SteinbergPerfectStatement.{u, v} : Prop :=
  ∀ (I : Type u) (R : Type v) [Fintype I] [DecidableEq I] [Ring R],
    3 ≤ Fintype.card I → commutator (SteinbergGroup I R) = ⊤

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.SteinbergPerfectStatement

/-- `SteinbergPerfectStatement` holds at every pair of universes. -/
theorem steinbergPerfectStatement.{u, v} : SteinbergPerfectStatement.{u, v} := by
  intro I R _ _ _ h
  exact steinberg_commutator_eq_top I R h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.steinbergPerfectStatement
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.steinbergPerfectStatement

/-- The rank-three case `St_3(R)` used by the padded-kill step. -/
theorem steinberg_fin_three_commutator_eq_top (R : Type*) [Ring R] :
    commutator (SteinbergGroup (Fin 3) R) = ⊤ :=
  steinberg_commutator_eq_top (Fin 3) R (by simp)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect.steinberg_fin_three_commutator_eq_top

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergPerfect
