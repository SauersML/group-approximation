import GroupApproximation.Computability.PresentationCodeCompleteness

/-!
# Codes from lists, and transport along an equality of relator sets

`PresentationCodeCompleteness.codeOf` builds the code of a `Finset` of
relators, and is `noncomputable`: `Finset.toList` is.  That is harmless when the
code is a fixed object named once, which is all that file needed --- but an
Adian--Rabin `transform` has to be a *computable* function into
`PresentationCode`, so the code it produces must be built from a `List` and
never from a `Finset`.

`codeOfList` is that version, and `relatorFinset_codeOfList` is its reading
lemma.  The two differ only in the source of the list, so the proof is the same
induction.

`presCongrSet` is the other piece of bookkeeping used everywhere downstream:
two presentations with *equal* relator sets present the same group, and the
equalities that arise --- a list's members, a `Finset`'s coercion, a relabelled
image --- are equalities of sets, not definitional identities.
-/

namespace GroupApproximation

/-- The members of a mapped list are the image of the members.

Deliberately in the root namespace rather than in `PresentationCodeList`: three
separate code constructions (`CoprodCode`, `RabinVariantCode`,
`BooneTowerPresentation`) each had a verbatim copy of this, and only two of the
three `open PresentationCodeList`.  Stated here, all three see it unqualified,
which is why none of their call sites had to change.

Nothing about it is specific to presentations — it is the list-to-set step that
every `relatorList`-to-relator-set argument goes through, which is why it kept
being rediscovered. -/
theorem setOf_mem_map {α β : Type} (f : α → β) (L : List α) :
    {x | x ∈ L.map f} = f '' {x | x ∈ L} := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]

namespace PresentationCodeList

open PresentationCodes

/-- **Transport along an equality of relator sets.** -/
def presCongrSet {α : Type} {s t : Set (FreeGroup α)} (h : s = t) :
    PresentedGroup s ≃* PresentedGroup t := h ▸ MulEquiv.refl _

@[simp] theorem presCongrSet_mk {α : Type} {s t : Set (FreeGroup α)} (h : s = t)
    (v : FreeGroup α) :
    presCongrSet h (PresentedGroup.mk s v) = PresentedGroup.mk t v := by
  subst h
  rfl

/-- The code naming a *list* of relators over an alphabet of size `m + 1`.
Unlike `codeOf` this is computable, which is what a reduction's `transform`
needs. -/
abbrev codeOfList {m : ℕ} (L : List (FreeGroup (Fin (m + 1)))) : PresentationCode :=
  (m, L.map encodeWord)

@[simp] theorem genCount_codeOfList {m : ℕ} (L : List (FreeGroup (Fin (m + 1)))) :
    genCount (codeOfList L) = m + 1 := rfl

theorem relatorFinset_codeOfList {m : ℕ} (L : List (FreeGroup (Fin (m + 1)))) :
    relatorFinset (codeOfList L) = L.toFinset := by
  classical
  have hlist : ∀ (l : List (List (ℕ × Bool)))
      (w : List (FreeGroup (Fin (m + 1)))),
      (w.map encodeWord).map (wordOf (m, l)) = w := by
    intro l w
    induction w with
    | nil => rfl
    | cons r t ih => simp only [List.map_cons, ih, wordOf_encodeWord]
  show ((L.map encodeWord).map (wordOf (m, L.map encodeWord))).toFinset = L.toFinset
  rw [hlist]

/-- The relator set of a list code, as a set: exactly the list's members. -/
theorem coe_relatorFinset_codeOfList {m : ℕ} (L : List (FreeGroup (Fin (m + 1)))) :
    ((relatorFinset (codeOfList L) : Finset (FreeGroup (Fin (genCount (codeOfList L)))))
      : Set (FreeGroup (Fin (genCount (codeOfList L))))) = {x | x ∈ L} := by
  rw [relatorFinset_codeOfList, List.coe_toFinset]

/-- **The group a list code presents.** -/
def carrierOfList {m : ℕ} (L : List (FreeGroup (Fin (m + 1)))) :
    Carrier (codeOfList L) ≃* PresentedGroup {x | x ∈ L} :=
  presCongrSet (coe_relatorFinset_codeOfList L)

/-! ## Reading an arbitrary code as a list

The relator *set* of any code is the set of members of an explicitly computable
list, namely the code's own second component read through `wordOf`.  This is
what lets a transformation consume a code it did not build. -/

/-- The relators of a code, as a computable list. -/
abbrev relatorListOf (c : PresentationCode) : List (FreeGroup (Fin (genCount c))) :=
  c.2.map (wordOf c)

theorem coe_relatorFinset (c : PresentationCode) :
    ((relatorFinset c : Finset (FreeGroup (Fin (genCount c))))
      : Set (FreeGroup (Fin (genCount c)))) = {x | x ∈ relatorListOf c} := by
  show (((relatorListOf c).toFinset : Finset (FreeGroup (Fin (genCount c))))
    : Set (FreeGroup (Fin (genCount c)))) = _
  rw [List.coe_toFinset]

/-- Any coded group is the group presented by its relator list. -/
def carrierEquivList (c : PresentationCode) :
    Carrier c ≃* PresentedGroup {x | x ∈ relatorListOf c} :=
  presCongrSet (coe_relatorFinset c)

end PresentationCodeList
end GroupApproximation
