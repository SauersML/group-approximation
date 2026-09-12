import GroupApproximation.Computability.OperatorMFMarkovWitness
import GroupApproximation.Computability.PresentationCodes

/-!
# The coding is onto finitely presented groups

`Computability.PresentationCodes` fixes a recursive datatype of finite
presentations and interprets it.  Interpretation alone is not enough for an
Adian--Rabin reduction: the coding also has to be *adequate*, in the sense
that every finitely presented group is named by some code.  Otherwise the
reduction could be vacuous --- a coding naming only trivial groups would
satisfy everything in `PresentationCodes` and support no reduction at all.

`exists_code_mulEquiv` is that adequacy statement, and it is proved by
reading the finite presentation off the class itself: `IsFinitelyPresented G`
unfolds to a surjection from a free group on `Fin n` whose kernel is the
normal closure of a finite set, so the finite set is encoded letter by letter
and the quotient identified.

The one wrinkle is the alphabet size.  A code names an alphabet of size
`c.1 + 1`, never zero, because `letterOf` has to be total.  So the degenerate
`n = 0` presentation --- which forces `G` trivial --- is handled separately by
a code that presents the trivial group outright.

## Consequence: the Markov witness

With adequacy, the two Markov witnesses transfer from groups to codes, giving
`markovWitness`.  That is the third of the four fields of
`MarkovMFConsequences.AdianRabinReduction`.  The fourth --- the computable
transformation together with its correctness equivalence --- is the
Adian--Rabin construction proper and remains open; it needs a finitely
presented group with undecidable word problem, which Mathlib does not have.
-/

namespace GroupApproximation
namespace PresentationCodes

open MarkovMFConsequences

/-! ## Encoding free-group elements -/

/-- The coded form of a free-group element over a `Fin` alphabet: its reduced
word, with each letter replaced by its index. -/
def encodeWord {n : ℕ} (r : FreeGroup (Fin n)) : List (ℕ × Bool) :=
  r.toWord.map fun p ↦ ((p.1 : ℕ), p.2)

theorem letterOf_val (m : ℕ) (l : List (List (ℕ × Bool))) (i : Fin (m + 1)) :
    letterOf (m, l) ((i : ℕ)) = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

/-- Reading a coded word recovers the element it was encoded from: letters of
the alphabet are below the alphabet size, so the reduction modulo that size is
the identity on them. -/
theorem wordOf_encodeWord (m : ℕ) (l : List (List (ℕ × Bool)))
    (r : FreeGroup (Fin (m + 1))) : wordOf (m, l) (encodeWord r) = r := by
  have hid : ∀ w : List (Fin (m + 1) × Bool),
      ((w.map fun p ↦ ((p.1 : ℕ), p.2)).map
        fun q ↦ (letterOf (m, l) q.1, q.2)) = w := by
    intro w
    induction w with
    | nil => rfl
    | cons p t ih => simp only [List.map_cons, ih, letterOf_val]
  calc wordOf (m, l) (encodeWord r)
      = FreeGroup.mk r.toWord := by
        simp only [wordOf, encodeWord, hid]
    _ = r := FreeGroup.mk_toWord

/-! ## The code naming a finite presentation -/

/-- The code naming a finite relator set over an alphabet of size `m + 1`.
Reducible for the same reason `genCount` is: `Fin (genCount (codeOf S))` has
to reduce to `Fin (m + 1)` for any statement about it to typecheck. -/
noncomputable abbrev codeOf {m : ℕ} (S : Finset (FreeGroup (Fin (m + 1)))) :
    PresentationCode :=
  (m, S.toList.map encodeWord)

theorem relatorFinset_codeOf {m : ℕ} (S : Finset (FreeGroup (Fin (m + 1)))) :
    relatorFinset (codeOf S) = S := by
  classical
  have hlist : ∀ (l : List (List (ℕ × Bool)))
      (w : List (FreeGroup (Fin (m + 1)))),
      (w.map encodeWord).map (wordOf (m, l)) = w := by
    intro l w
    induction w with
    | nil => rfl
    | cons r t ih =>
      simp only [List.map_cons, ih, wordOf_encodeWord]
  show ((S.toList.map encodeWord).map
    (wordOf (m, S.toList.map encodeWord))).toFinset = S
  rw [hlist, Finset.toList_toFinset]

/-! ## The degenerate alphabet -/

/-- A code presenting the trivial group: one generator, and that generator as
the only relator. -/
noncomputable abbrev trivialCode : PresentationCode :=
  codeOf ({FreeGroup.of (0 : Fin 1)} : Finset (FreeGroup (Fin 1)))

theorem normalClosure_trivialCode :
    Subgroup.normalClosure
        ((relatorFinset trivialCode : Finset (FreeGroup (Fin 1))) :
          Set (FreeGroup (Fin 1))) = ⊤ := by
  classical
  rw [relatorFinset_codeOf]
  refine top_unique ?_
  rw [← FreeGroup.closure_range_of (Fin 1), Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst hi
  exact Subgroup.subset_normalClosure (by simp)

theorem subsingleton_carrier_trivialCode : Subsingleton (Carrier trivialCode) := by
  haveI : Subsingleton (FreeGroup (Fin 1) ⧸ (⊤ : Subgroup (FreeGroup (Fin 1)))) :=
    QuotientGroup.subsingleton_quotient_top
  constructor
  intro a b
  exact (QuotientGroup.quotientMulEquivOfEq
    normalClosure_trivialCode).injective (Subsingleton.elim _ _)

/-! ## Adequacy -/

/-- **Every finitely presented group is named by a code.**  This is what makes
the coding an adequate syntax for finite presentations, and hence a possible
source for an Adian--Rabin reduction. -/
theorem exists_code_mulEquiv (G : Type) [Group G] [Group.IsFinitelyPresented G] :
    ∃ c : PresentationCode, Nonempty (Carrier c ≃* G) := by
  classical
  obtain ⟨n, φ, hsurj, hfng⟩ := (‹Group.IsFinitelyPresented G›).out
  obtain ⟨S, hSfin, hSclosure⟩ := hfng
  cases n with
  | zero =>
    have htriv : ∀ w : FreeGroup (Fin 0), w = 1 := by
      intro w
      have hw : w.toWord = [] := by
        rcases h : w.toWord with _ | ⟨p, t⟩
        · rfl
        · exact p.1.elim0
      calc w = FreeGroup.mk w.toWord := FreeGroup.mk_toWord.symm
        _ = 1 := by rw [hw]; rfl
    haveI : Subsingleton G := by
      constructor
      intro a b
      obtain ⟨wa, rfl⟩ := hsurj a
      obtain ⟨wb, rfl⟩ := hsurj b
      rw [htriv wa, htriv wb]
    haveI := subsingleton_carrier_trivialCode
    exact ⟨trivialCode, ⟨⟨⟨fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩,
      fun _ _ ↦ Subsingleton.elim _ _⟩⟩⟩
  | succ m =>
    refine ⟨codeOf hSfin.toFinset, ⟨?_⟩⟩
    have hnorm : Subgroup.normalClosure
        ((relatorFinset (codeOf hSfin.toFinset) :
            Finset (FreeGroup (Fin (m + 1)))) :
          Set (FreeGroup (Fin (m + 1)))) = φ.ker := by
      rw [relatorFinset_codeOf, Set.Finite.coe_toFinset, hSclosure]
    exact (QuotientGroup.quotientMulEquivOfEq hnorm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

/-! ## The Markov witness at this coding -/

/-- A code for the trivial group, obtained from adequacy. -/
noncomputable abbrev positiveCode : PresentationCode :=
  (exists_code_mulEquiv PUnit.{1}).choose

/-- A code for the manuscript's finitely presented non-MF group, obtained from
adequacy. -/
noncomputable abbrev negativeCode : PresentationCode :=
  (exists_code_mulEquiv ChosenMarkedPresentation.MarkedGroup).choose

theorem isOperatorMF_positiveCode : IsOperatorMF (Carrier positiveCode) := by
  obtain ⟨ep⟩ := (exists_code_mulEquiv PUnit.{1}).choose_spec
  exact (OperatorMFMarkovWitness.positive_punit.2).comap
    ep.toMonoidHom ep.injective

theorem not_isOperatorMF_negativeCode :
    ¬ IsOperatorMF (Carrier negativeCode) := by
  obtain ⟨en⟩ :=
    (exists_code_mulEquiv ChosenMarkedPresentation.MarkedGroup).choose_spec
  intro h
  exact ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF.2
    (h.comap en.symm.toMonoidHom en.symm.injective)

/-- **The Markov witness, transported from groups to codes.**  The positive
side is the trivial group and the negative side is the manuscript's finitely
presented non-MF group; adequacy supplies codes for both.  This is the third
of the four fields of an `AdianRabinReduction`. -/
noncomputable def markovWitness :
    MarkovWitness (operatorMFProperty semantics) where
  positiveCode := positiveCode
  positive := isOperatorMF_positiveCode
  negativeCode := negativeCode
  negative := not_isOperatorMF_negativeCode

end PresentationCodes
end GroupApproximation
