import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Algebra.GroupTorsionFree
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Data.ZMod.Basic

/-!
# Torsion-freeness is a Markov property, so recognising it is undecidable

`Sofic.FournierFacioUniversalGroup` explains, in prose, why the repository's
own explicit countable universal torsion-free group cannot be fed to Higman's
embedding theorem: it is indexed by

  `{c // IsPowerTorsionFree (CodedPresentedGroup c)}`,

and *that set is not recursive, because torsion-freeness is a Markov property
and Adian--Rabin makes it undecidable*.  With
`Computability.AdianRabinGeneral` that sentence is now a theorem rather than a
remark, and this file proves it.

The three Markov clauses are all available:

* heredity is `IsPowerTorsionFree.comap`, already proved;
* free groups are torsion-free --- Mathlib's
  `IsMulTorsionFree (FreeGroup α)` instance, through
  `IsPowerTorsionFree.of_isMulTorsionFree`;
* the trivial group is torsion-free and the two-element cyclic group is not,
  which supplies the positive and forbidden codes.

`torsionFree_recognition_undecidable_of_wordProblem` is the conclusion, and
`not_recursive_torsionFreeCodes` is the statement `FournierFacioUniversalGroup`
appeals to: the index set of the explicit universal group is not decidable.

## Manuscript status

Records, as a theorem, the obstruction that blocks the Chiodo/Belegradek row
of `metadata/LITERATURE_QUARANTINE.md` from being discharged by the
repository's own universal group.
-/

namespace GroupApproximation
namespace TorsionFreeMarkov

open PresentationCodes AdianRabinGeneral

/-! ## A finitely presented group with torsion -/

/-- The single relator `x²`. -/
def torsionRels : Set (FreeGroup (Fin 1)) := {FreeGroup.of (0 : Fin 1) ^ 2}

/-- One relator is a finite set of relators. -/
instance : Finite (torsionRels : Set (FreeGroup (Fin 1))) :=
  Set.Finite.to_subtype (Set.finite_singleton _)

/-- The two-element cyclic group, as a presented group. -/
abbrev TorsionGroup : Type := PresentedGroup torsionRels

/-- The generator of the two-element group. -/
def c2gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem c2gen_sq : c2gen ^ 2 = 1 := by decide

theorem c2gen_ne_one : c2gen ≠ 1 := by decide

/-- The relator dies in the two-element group. -/
theorem lift_torsionRels (r : FreeGroup (Fin 1)) (hr : r ∈ torsionRels) :
    FreeGroup.lift (fun _ : Fin 1 ↦ c2gen) r = 1 := by
  have hr' : r = FreeGroup.of (0 : Fin 1) ^ 2 := hr
  subst hr'
  rw [map_pow, FreeGroup.lift_apply_of]
  exact c2gen_sq

/-- The comparison homomorphism onto the two-element group. -/
def toC2 : TorsionGroup →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup lift_torsionRels

theorem toC2_of : toC2 (PresentedGroup.of (0 : Fin 1)) = c2gen :=
  PresentedGroup.toGroup.of _

/-- The generator survives. -/
theorem gen_ne_one : (PresentedGroup.of (0 : Fin 1) : TorsionGroup) ≠ 1 := by
  intro h
  apply c2gen_ne_one
  rw [← toC2_of, h, map_one]

/-- The generator squares to the identity. -/
theorem gen_sq : (PresentedGroup.of (0 : Fin 1) : TorsionGroup) ^ 2 = 1 := by
  have hmem : FreeGroup.of (0 : Fin 1) ^ 2 ∈ torsionRels := rfl
  have h : PresentedGroup.mk torsionRels (FreeGroup.of (0 : Fin 1) ^ 2) = 1 :=
    PresentedGroup.one_of_mem hmem
  rw [map_pow] at h
  exact h

/-- **The two-element group has torsion.** -/
theorem not_isPowerTorsionFree_torsionGroup :
    ¬ IsPowerTorsionFree TorsionGroup := by
  intro h
  exact gen_ne_one (h _ 2 (by norm_num) gen_sq)

/-! ## The Markov data -/

/-- A code for a group with torsion. -/
noncomputable def forbiddenCode : PresentationCode :=
  (exists_code_mulEquiv TorsionGroup).choose

theorem not_isPowerTorsionFree_forbiddenCode :
    ¬ IsPowerTorsionFree (Carrier forbiddenCode) := by
  obtain ⟨e⟩ := (exists_code_mulEquiv TorsionGroup).choose_spec
  intro h
  exact not_isPowerTorsionFree_torsionGroup
    (h.comap e.symm.toMonoidHom e.symm.injective)

theorem isPowerTorsionFree_trivialCode :
    IsPowerTorsionFree (Carrier trivialCode) := by
  haveI := subsingleton_carrier_trivialCode
  intro g n _ _
  exact Subsingleton.elim g 1

/-- **Torsion-freeness is a Markov property.** -/
noncomputable def torsionFreeMarkovData :
    MarkovData (fun (H : Type) (_ : Group H) ↦ IsPowerTorsionFree H) where
  hereditary f hf hK := IsPowerTorsionFree.comap hK f hf
  free _ _ := IsPowerTorsionFree.of_isMulTorsionFree
  positiveCode := trivialCode
  positive := isPowerTorsionFree_trivialCode
  forbidden := forbiddenCode
  forbidden_not := not_isPowerTorsionFree_forbiddenCode

/-! ## Undecidability -/

/-- **Recognising torsion-freeness from a finite presentation is
undecidable**, given only that the word problem is. -/
theorem torsionFree_recognition_undecidable_of_wordProblem
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred
      (codeProperty (fun (H : Type) (_ : Group H) ↦ IsPowerTorsionFree H)) :=
  recognition_undecidable_of_wordProblem torsionFreeMarkovData h

/-- The set of codes presenting torsion-free groups is not decidable.  This is
the sentence `Sofic.FournierFacioUniversalGroup` appeals to when it explains
why the explicit countable universal torsion-free group is not recursively
presented. -/
theorem not_recursive_torsionFreeCodes
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred (fun c : PresentationCode ↦ IsPowerTorsionFree (Carrier c)) :=
  torsionFree_recognition_undecidable_of_wordProblem h

/-- The negative side is not even recursively enumerable. -/
theorem torsionFree_negative_side_not_re_of_wordProblem
    (h : ¬ REPred (fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x)) :
    ¬ REPred (fun c ↦ ¬ IsPowerTorsionFree (Carrier c)) :=
  negative_side_not_re_of_wordProblem torsionFreeMarkovData h

end TorsionFreeMarkov
end GroupApproximation
