import GroupApproximation.Algebra.RabinVariantPresentation
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Computability.PresentationCodeList
import GroupApproximation.Computability.RabinVariantMF
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The variant construction in a generator numbering

`Algebra.RabinVariantPresentation` builds its group on `Gen m = Fin m ⊕ Extra m`
--- the source generators, the free letter `s`, one killing letter `tᵢ` per
index, and the four cascade letters `u, b, c, k`.  A presentation *code* numbers
its generators by `Fin (n + 1)`, so before the construction can be the
`transform` of an Adian--Rabin reduction it has to be renumbered.

Two things are needed, and both are bookkeeping:

* `genEquiv`, an explicit equivalence `Gen m ≃ Fin (m + (m + 5) + 1)`.  It is
  built from `finSumFinEquiv` and one hand-written equivalence
  `Extra m ≃ Fin (m + 1) ⊕ Fin 5`, so it is computable --- which matters,
  because the code it produces has to be a computable function of the input.
* `relatorList`, the relators as a `List` rather than a `Set`, together with the
  proof that the list's members are exactly `relators`.  The construction is
  stated for a `Set` because nothing in the group theory cares; a code needs the
  finite list.

Nothing here is about MF or about undecidability.  It is the change of
coordinates that lets the group-theoretic biconditional already proved in
`Algebra.RabinVariantPresentation` and `Computability.RabinVariantMF` be read as
a statement about codes.
-/

namespace GroupApproximation
namespace RabinVariantCode

open RabinVariantPresentation PresentationCodes PresentationCodeList
open PresentedGroupRelabel

variable {m : ℕ}

/-! ## Numbering the generators -/

/-- The adjoined letters, numbered: the `m + 1` killing letters first, then
`s, u, b, c, k`. -/
def extraEquiv (m : ℕ) : Extra m ≃ Fin (m + 1) ⊕ Fin 5 where
  toFun
    | Extra.s => Sum.inr 0
    | Extra.t j => Sum.inl j
    | Extra.u => Sum.inr 1
    | Extra.b => Sum.inr 2
    | Extra.c => Sum.inr 3
    | Extra.k => Sum.inr 4
  invFun := Sum.elim Extra.t ![Extra.s, Extra.u, Extra.b, Extra.c, Extra.k]
  left_inv e := by cases e <;> rfl
  right_inv x := by
    rcases x with j | i
    · rfl
    · fin_cases i <;> rfl

/-- **The generator numbering.**  The source generators keep their numbers, and
the adjoined letters follow.  The count is written `m + (m + 5) + 1` because
that is the shape `PresentationCodes.genCount` produces. -/
def genEquiv (m : ℕ) : Gen m ≃ Fin (m + (m + 5) + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) ((extraEquiv m).trans finSumFinEquiv)).trans
    finSumFinEquiv

/-! ## The relators as a list

The three families of `relators` become three list segments.  `List.finRange`
enumerates the killing letters. -/

/-- The relators of the construction, as a list. -/
def relatorList (R : List (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    List (FreeGroup (Gen m)) :=
  R.map (fun r => emb r) ++
    (List.finRange (m + 1)).map (fun i => U * T i * U⁻¹ * (T i * sWord i)⁻¹) ++
    [B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹, C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹,
      K * Z w * K⁻¹ * C⁻¹]

/-- **The list spells the relator set.**  Everything downstream is stated for
`relators`, a `Set`; a code needs the list, and this says they agree. -/
theorem mem_relatorList (R : List (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    {x | x ∈ relatorList R w} = relators {r | r ∈ R} w := by
  ext x
  simp only [relatorList, relators, Set.mem_setOf_eq, List.mem_append, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, Set.mem_union, Set.mem_image,
    Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_finRange,
    true_and]

/-! ## The code of the construction

Everything above is bookkeeping; this is where it is spent.  A code `c` and a
word `w` determine the construction applied to the group `c` presents, and the
result is again a code --- built from lists throughout, so that it is a
computable function of `(c, w)`. -/

/-- The relators of the construction over a code's group, renumbered. -/
def variantRelators (c : PresentationCode) (w : List (ℕ × Bool)) :
    List (FreeGroup (Fin (genCount c + (genCount c + 5) + 1))) :=
  (relatorList (relatorListOf c) (wordOf c w)).map (relabel (genEquiv (genCount c)))

/-- **The code the construction outputs.** -/
abbrev variantCode (c : PresentationCode) (w : List (ℕ × Bool)) : PresentationCode :=
  codeOfList (variantRelators c w)

/-- **The code presents the group the construction builds.** -/
noncomputable def variantCodeEquiv (c : PresentationCode) (w : List (ℕ × Bool)) :
    Carrier (variantCode c w) ≃* Pres {x | x ∈ relatorListOf c} (wordOf c w) :=
  ((carrierOfList (variantRelators c w)).trans
      (presCongrSet (setOf_mem_map _ _))).trans
    (((congrEquiv (genEquiv (genCount c))
        {x | x ∈ relatorList (relatorListOf c) (wordOf c w)}).symm).trans
      (presCongrSet (mem_relatorList _ _)))

/-- **The relator set of the construction's code**, as a renumbering of the
construction's relators.  The analogue of `CoprodCode.relSet_coprodCode`, and
what lets a differently-built code with the same relator set be recognised as
presenting the same group. -/
theorem relSet_variantCode (c : PresentationCode) (w : List (ℕ × Bool)) :
    {x | x ∈ relatorListOf (variantCode c w)}
      = relabelRels (genEquiv (genCount c))
          (relators {x | x ∈ relatorListOf c} (wordOf c w)) := by
  have h1 : {x | x ∈ relatorListOf (variantCode c w)}
      = {x | x ∈ variantRelators c w} := by
    rw [← coe_relatorFinset, coe_relatorFinset_codeOfList]
  rw [h1, variantRelators, setOf_mem_map, mem_relatorList]
  rfl

/-- **The collapse clause, at codes.**  When the word dies in the group the
input code presents, the output code presents a free group, hence an
operator-MF one. -/
theorem variantCode_isOperatorMF (c : PresentationCode) (w : List (ℕ × Bool))
    (hw : PresentedGroup.mk {x | x ∈ relatorListOf c} (wordOf c w) = 1) :
    IsOperatorMF (Carrier (variantCode c w)) :=
  (RabinVariantMF.pres_isOperatorMF _ _ hw).comap
    (variantCodeEquiv c w).toMonoidHom (variantCodeEquiv c w).injective

/-- **The embedding clause, at codes.**  When the word survives, the input
group embeds in the output group, so operator-MF descends from one to the
other. -/
theorem isOperatorMF_of_variantCode (c : PresentationCode) (w : List (ℕ × Bool))
    (hw : PresentedGroup.mk {x | x ∈ relatorListOf c} (wordOf c w) ≠ 1)
    (hMF : IsOperatorMF (Carrier (variantCode c w))) : IsOperatorMF (Carrier c) := by
  have h1 : IsOperatorMF (Pres {x | x ∈ relatorListOf c} (wordOf c w)) :=
    hMF.comap (variantCodeEquiv c w).symm.toMonoidHom (variantCodeEquiv c w).symm.injective
  have h3 : IsOperatorMF (PresentedGroup {x | x ∈ relatorListOf c}) :=
    h1.comap (srcToPres _ _) (srcToPres_injective_of_ne_one _ _ hw)
  exact h3.comap (carrierEquivList c).toMonoidHom (carrierEquivList c).injective

end RabinVariantCode
end GroupApproximation
