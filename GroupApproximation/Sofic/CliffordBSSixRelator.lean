import GroupApproximation.Monsters.LiteralCyclicCalibration
import GroupApproximation.Sofic.CompressionDefectSquare

/-!
# Deleting the redundant square relator of `E_BS`

`non_mf_groups_exist.tex`, proof of `thm:C` (grep `"six-relator presentation"`,
never a line number: the file is edited concurrently).  The proof opens:

> As with `w`, the relator `w_BS² = 1` is redundant: `t c t⁻¹` and
> `γ₀ (t c t⁻¹) γ₀⁻¹` are involutions, so centrality forces it by the
> involution-reversal identity.  Deleting it gives a six-relator presentation
> of the same group.

`Monsters.LiteralCyclicCalibration` formalizes the seven-relator presentation
and *uses* the redundancy downstream, but it never states that sentence: the
six-relator presentation is written nowhere, and nothing says it presents the
same group.  This module supplies exactly the missing sentence.

`SixGroup` is presented by the manuscript's list with `markedSqRelator` struck
out --- six relators, displayed in `relatorsSixList` in the printed order ---
and `sixTietzeEquiv` is an isomorphism `SixGroup ≃* LiteralGroup` carrying each
generator to the generator of the same name and the marked word to the marked
word.  Both halves are the elementary Tietze argument:

* the six relators of `SixGroup` are among the seven of `LiteralGroup`, so the
  seven-relator group receives a map from the six-relator one for free;
* conversely the deleted relator *holds* in `SixGroup`: the three surviving
  commutation relators make the mark central, the surviving `c² = 1` makes
  `t c t⁻¹` an involution, and
  `markedCompressionWord_sq_eq_one_of_c_sq_of_central` --- the Lean form of the
  manuscript's involution-reversal identity `d w d⁻¹ = w⁻¹` --- then applies.

Nothing analytic is used or claimed here.  The file is finite-presentation
bookkeeping, stated on the *same* `Generator`, `markedWord` and `relators` as
`LiteralCyclicCalibration` so that the two presentations are literally the
manuscript's two.
-/

namespace GroupApproximation
namespace CliffordBSSixRelator

open LiteralCyclicCalibration

noncomputable section

/-! ## The six-relator presentation -/

/-- The manuscript's relator list with the square relator `w_BS² = 1` deleted,
in the printed order.  Its length is six: that is the assertion "deleting it
gives a six-relator presentation". -/
def relatorsSixList : List (FreeGroup Generator) :=
  [stableRelator, lampSqRelator, lampGammaRelator,
    markedGammaRelator, markedStableRelator, markedLampRelator]

theorem relatorsSixList_length : relatorsSixList.length = 6 := by
  simp [relatorsSixList]

/-- The six surviving relators as a set.  A `Set` rather than a `Finset`
because `PresentedGroup` consumes a set, and no decidable equality on
`FreeGroup Generator` is then needed anywhere below. -/
def relatorsSix : Set (FreeGroup Generator) :=
  {stableRelator, lampSqRelator, lampGammaRelator,
    markedGammaRelator, markedStableRelator, markedLampRelator}

theorem relatorsSix_eq_setOf_mem_list :
    relatorsSix = {w | w ∈ relatorsSixList} := by
  ext w
  simp [relatorsSix, relatorsSixList]

theorem relatorsSix_finite : relatorsSix.Finite := by
  unfold relatorsSix
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  exact Set.finite_singleton _

instance relatorsSix_finite_coe : Finite (relatorsSix : Set (FreeGroup Generator)) :=
  relatorsSix_finite.to_subtype

/-- **The six-relator presentation of `E_BS`.**  Same three generators, same
relators, with `w_BS² = 1` struck out. -/
abbrev SixGroup : Type := PresentedGroup relatorsSix

/-- Three generators and six relators, so the deleted presentation is finitely
presented on its own terms rather than by transport. -/
instance sixGroup_finitelyPresented : Group.IsFinitelyPresented SixGroup :=
  inferInstance

abbrev evalSix : FreeGroup Generator →* SixGroup := PresentedGroup.mk _

abbrev gammaSix : SixGroup := evalSix gammaWord
abbrev stableSix : SixGroup := evalSix stableWord
abbrev lampSix : SixGroup := evalSix lampWord
abbrev markSix : SixGroup := evalSix markedWord

/-! ## The deleted relator holds in the six-relator group

This is the manuscript's redundancy argument, verbatim: the surviving
`c² = 1` makes `d = t c t⁻¹` an involution, the three surviving commutation
relators make the mark central, and the involution-reversal identity closes the
loop. -/

theorem lampSix_sq : lampSix ^ 2 = 1 := by
  change evalSix lampSqRelator = 1
  exact PresentedGroup.one_of_mem (by simp [relatorsSix])

theorem markSix_comm_gamma : Commute markSix gammaSix := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalSix markedGammaRelator = 1
  exact PresentedGroup.one_of_mem (by simp [relatorsSix])

theorem markSix_comm_stable : Commute markSix stableSix := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalSix markedStableRelator = 1
  exact PresentedGroup.one_of_mem (by simp [relatorsSix])

theorem markSix_comm_lamp : Commute markSix lampSix := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalSix markedLampRelator = 1
  exact PresentedGroup.one_of_mem (by simp [relatorsSix])

/-- The three surviving commutation relators still make the mark central: they
say it commutes with a generating set, and a presented group is generated by
its generators. -/
theorem markSix_central (g : SixGroup) : Commute markSix g := by
  have hgen : ∀ i : Generator, Commute markSix (evalSix (FreeGroup.of i)) := by
    intro i
    fin_cases i
    · exact markSix_comm_gamma
    · exact markSix_comm_stable
    · exact markSix_comm_lamp
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i => exact hgen i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

theorem markSix_eq_markedCompressionWord :
    markSix = markedCompressionWord stableSix gammaSix lampSix := by
  simp [markSix, markedWord, displacedLampWord, commutatorWord,
    markedCompressionWord, commutatorElement_def]

/-- **The deleted relator is a theorem of the six-relator group.**  This is the
manuscript's sentence "the relator `w_BS² = 1` is redundant", by the
involution-reversal identity it cites.  Nothing about the seven-relator group
enters the proof. -/
theorem markSix_sq : markSix ^ 2 = 1 := by
  rw [markSix_eq_markedCompressionWord]
  refine markedCompressionWord_sq_eq_one_of_c_sq_of_central
    stableSix gammaSix lampSix lampSix_sq ?_
  intro g
  rw [← markSix_eq_markedCompressionWord]
  exact markSix_central g

/-! ## The two presentations define the same group -/

/-- Evaluating the free group at the generators of a presented group is the
quotient map.  The two `PresentedGroup.toGroup` obligations below are phrased
with `FreeGroup.lift`, and this is what turns them into statements about
`PresentedGroup.mk`, where `one_of_mem` applies. -/
theorem lift_of_eq_mk (R : Set (FreeGroup Generator)) :
    FreeGroup.lift
        (fun i : Generator => (PresentedGroup.of i : PresentedGroup R)) =
      PresentedGroup.mk R :=
  FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of

theorem lift_of_apply (R : Set (FreeGroup Generator))
    (w : FreeGroup Generator) :
    FreeGroup.lift
        (fun i : Generator => (PresentedGroup.of i : PresentedGroup R)) w =
      PresentedGroup.mk R w :=
  DFunLike.congr_fun (lift_of_eq_mk R) w

/-- The six surviving relators are among the seven printed ones, so they hold
in the seven-relator group. -/
theorem literal_kills_relatorsSix :
    ∀ r ∈ relatorsSix,
      FreeGroup.lift
        (fun i : Generator => (PresentedGroup.of i : LiteralGroup)) r = 1 := by
  intro r hr
  rw [lift_of_apply]
  simp only [relatorsSix, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact PresentedGroup.one_of_mem (by simp [relators])

/-- All seven printed relators hold in the six-relator group: six of them by
fiat, and the deleted square relator by `markSix_sq`.  This is the direction
that carries the manuscript's redundancy argument. -/
theorem six_kills_relators :
    ∀ r ∈ relators,
      FreeGroup.lift
        (fun i : Generator => (PresentedGroup.of i : SixGroup)) r = 1 := by
  intro r hr
  rw [lift_of_apply]
  simp [relators] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])
  · show PresentedGroup.mk relatorsSix (markedWord ^ 2) = 1
    rw [map_pow]
    exact markSix_sq
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])
  · exact PresentedGroup.one_of_mem (by simp [relatorsSix])

/-- The six-relator group maps to the seven-relator group, generator to
generator. -/
def toLiteral : SixGroup →* LiteralGroup :=
  PresentedGroup.toGroup literal_kills_relatorsSix

/-- The seven-relator group maps to the six-relator group, generator to
generator. -/
def ofLiteral : LiteralGroup →* SixGroup :=
  PresentedGroup.toGroup six_kills_relators

@[simp] theorem toLiteral_of (i : Generator) :
    toLiteral (PresentedGroup.of i) = PresentedGroup.of i :=
  PresentedGroup.toGroup.of _

@[simp] theorem ofLiteral_of (i : Generator) :
    ofLiteral (PresentedGroup.of i) = PresentedGroup.of i :=
  PresentedGroup.toGroup.of _

theorem toLiteral_comp_evalSix :
    (toLiteral : SixGroup →* LiteralGroup).comp evalSix = evalWord :=
  FreeGroup.ext_hom _ _ fun i => toLiteral_of i

theorem ofLiteral_comp_evalWord :
    (ofLiteral : LiteralGroup →* SixGroup).comp evalWord = evalSix :=
  FreeGroup.ext_hom _ _ fun i => ofLiteral_of i

/-- The six-relator quotient map composed with `toLiteral` is the seven-relator
quotient map: the isomorphism below is the identity on words, not merely some
abstract isomorphism. -/
theorem toLiteral_evalSix (w : FreeGroup Generator) :
    toLiteral (evalSix w) = evalWord w :=
  DFunLike.congr_fun toLiteral_comp_evalSix w

theorem ofLiteral_evalWord (w : FreeGroup Generator) :
    ofLiteral (evalWord w) = evalSix w :=
  DFunLike.congr_fun ofLiteral_comp_evalWord w

theorem ofLiteral_comp_toLiteral :
    ofLiteral.comp toLiteral = MonoidHom.id SixGroup :=
  PresentedGroup.ext fun i => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, toLiteral_of,
      ofLiteral_of, MonoidHom.id_apply]

theorem toLiteral_comp_ofLiteral :
    toLiteral.comp ofLiteral = MonoidHom.id LiteralGroup :=
  PresentedGroup.ext fun i => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, ofLiteral_of,
      toLiteral_of, MonoidHom.id_apply]

/-- **Deleting the redundant square relator gives a presentation of the same
group.**  The isomorphism is the identity on generators in both directions, so
it is the Tietze move the manuscript performs. -/
def sixTietzeEquiv : SixGroup ≃* LiteralGroup where
  toFun := toLiteral
  invFun := ofLiteral
  left_inv := fun x => by
    simpa using DFunLike.congr_fun ofLiteral_comp_toLiteral x
  right_inv := fun x => by
    simpa using DFunLike.congr_fun toLiteral_comp_ofLiteral x
  map_mul' := map_mul toLiteral

@[simp] theorem sixTietzeEquiv_apply (x : SixGroup) :
    sixTietzeEquiv x = toLiteral x := rfl

@[simp] theorem sixTietzeEquiv_symm_apply (x : LiteralGroup) :
    sixTietzeEquiv.symm x = ofLiteral x := rfl

theorem sixTietzeEquiv_gamma : sixTietzeEquiv gammaSix = gamma :=
  toLiteral_evalSix gammaWord

theorem sixTietzeEquiv_stable : sixTietzeEquiv stableSix = stable :=
  toLiteral_evalSix stableWord

theorem sixTietzeEquiv_lamp : sixTietzeEquiv lampSix = lamp :=
  toLiteral_evalSix lampWord

/-- The isomorphism carries the marked word to the marked word, so every
statement `LiteralCyclicCalibration` proves about `mark` is a statement about
the six-relator group's mark. -/
theorem sixTietzeEquiv_mark : sixTietzeEquiv markSix = mark :=
  toLiteral_evalSix markedWord

/-- The mark of the six-relator presentation is nontrivial, transported from
`LiteralCyclicCalibration.mark_ne_one`. -/
theorem markSix_ne_one : markSix ≠ 1 := by
  intro h
  apply mark_ne_one
  rw [← sixTietzeEquiv_mark, h, map_one]

/-! ## The manuscript sentence -/

/-- **`thm:C`, proof, opening sentence.**  The square relator `w_BS² = 1` is a
consequence of the other six; the six-relator list is displayed, has length
six, and presents a group isomorphic to the seven-relator group by an
isomorphism that is the identity on the three printed generators and carries
the marked word to the marked word.

The redundancy clause is `markSix_sq`, obtained from `lampSix_sq` (the
surviving `c² = 1`) and `markSix_central` (the three surviving commutation
relators) through the manuscript's involution-reversal identity. -/
theorem manuscriptSixRelatorSameGroup :
    relatorsSixList =
        [stableRelator, lampSqRelator, lampGammaRelator,
          markedGammaRelator, markedStableRelator, markedLampRelator] ∧
      relatorsSixList.length = 6 ∧
      relatorsSix = {w | w ∈ relatorsSixList} ∧
      markSix ^ 2 = 1 ∧
      Group.IsFinitelyPresented SixGroup ∧
      ∃ e : SixGroup ≃* LiteralGroup,
        e gammaSix = gamma ∧ e stableSix = stable ∧ e lampSix = lamp ∧
          e markSix = mark :=
  ⟨rfl, relatorsSixList_length, relatorsSix_eq_setOf_mem_list, markSix_sq,
    inferInstance,
    sixTietzeEquiv, sixTietzeEquiv_gamma, sixTietzeEquiv_stable,
    sixTietzeEquiv_lamp, sixTietzeEquiv_mark⟩

end

end CliffordBSSixRelator
end GroupApproximation
