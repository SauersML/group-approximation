import GroupApproximation.GGT.HullEeOneStep

/-!
# Reading one word in the other relative generating set

`GGT/HullEeOneStep.lean` leaves `EeLocalFiniteness` as the last clause of Hull's
Lemma `ee`, and the obstacle to attacking it is not the geometry but a change of
vocabulary.  The two relative generating sets share an alphabet
(`alphabet_eq_relGenSetAddSubgroup`) but disagree about which letters are
peripheral:

| element of        | in the enlargement `X ∪ E` / `{H_λ}` | in `D_E`, base `X ∪ ⋃H_λ` / family `E` |
| ----------------- | ------------------------------------ | -------------------------------------- |
| `X`               | base letter                          | base letter                            |
| `E`               | **base** letter                      | **component** letter                   |
| `H_μ`             | **component** letter                 | **base** letter                        |

So a word is spelled over `RelLetter G Λ` on one side and over
`RelLetter G Unit` on the other, and the isolated-component estimate --- which is
about `E`-components --- can only be applied after the word has been transported.
`transferLetter` is that transport, and this module proves the four things any
consumer of it needs: it preserves the group element a letter names, hence the
element a word spells and every vertex of the path it traces; it carries
admissible letters to admissible letters; and it turns exactly the `E`-letters
into components.

## The one real choice

A base letter of the enlargement may lie in `X`, in `E`, or in both, and the
translation has to pick.  It sends a base letter to a component **whenever the
letter lies in `E`**, which is decided classically --- membership in a subgroup
carries no decidability.  Hence `noncomputable`, which costs nothing here: the
translation exists to be reasoned about, never to be run.

The choice is the right one for the consumer.  What the estimate needs is that
every `E`-letter has become a component, so that the bound applies to it; a
letter of `X ∩ E` sent to a component is harmless, because
`isLetter_transferLetter` checks it against `D_E.fam` and finds it there.  Sending
it the other way would leave an `E`-letter uncounted, which is the failure the
argument cannot survive.

## What is deliberately not here

`AvoidsFrom` is **not** transported.  The avoidance in play is avoidance of
`Γ_{H_λ}`, a condition about the ORIGINAL family, and it is read on the original
word throughout Hull's argument; the transported word is used only to name the
`E`-components and feed the estimate.  Transporting avoidance would be
meaningless --- `D_E`'s family is `E`, not `H_λ` --- and stating it would invite
exactly the confusion this module exists to prevent.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Transfer

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  The translation -/

open Classical in
/-- **A letter of the enlargement, read in `D_E`.**

A base letter lying in `E` becomes the `E`-component letter it names; any other
base letter stays a base letter; and a peripheral letter becomes a base letter,
`⋃H_λ` being part of `D_E`'s base.

Classical, and so `noncomputable`, because membership in a subgroup is not
decidable.  Nothing here is ever evaluated. -/
noncomputable def transferLetter (E : Subgroup G) :
    RelLetter G Λ → RelLetter G Unit
  | RelLetter.base x => if x ∈ E then RelLetter.comp () x else RelLetter.base x
  | RelLetter.comp _ h => RelLetter.base h

theorem transferLetter_base_of_mem {E : Subgroup G} {x : G} (hx : x ∈ E) :
    transferLetter (Λ := Λ) E (RelLetter.base x) = RelLetter.comp () x := by
  simp only [transferLetter]
  exact if_pos hx

theorem transferLetter_base_of_notMem {E : Subgroup G} {x : G} (hx : x ∉ E) :
    transferLetter (Λ := Λ) E (RelLetter.base x) = RelLetter.base x := by
  simp only [transferLetter]
  exact if_neg hx

@[simp] theorem transferLetter_comp (E : Subgroup G) (lam : Λ) (h : G) :
    transferLetter E (RelLetter.comp lam h) = RelLetter.base h := rfl

/-! ## 2.  The element a letter names is unchanged -/

/-- **The translation renames letters, not elements.**  Every clause of
`transferLetter` keeps the group element, which is what makes the transported
word spell the same thing and trace the same path. -/
theorem val_transferLetter (E : Subgroup G) (a : RelLetter G Λ) :
    (transferLetter E a).val = a.val := by
  cases a with
  | base x =>
      by_cases hx : x ∈ E
      · simp only [transferLetter_base_of_mem hx, RelLetter.val]
      · simp only [transferLetter_base_of_notMem hx, RelLetter.val]
  | comp lam h => rfl

/-- **A transported word spells what the original spelled.** -/
theorem listVal_map_transferLetter (E : Subgroup G) (w : List (RelLetter G Λ)) :
    RelLetter.listVal (w.map (transferLetter E)) = RelLetter.listVal w := by
  show ((w.map (transferLetter E)).map RelLetter.val).prod
      = (w.map RelLetter.val).prod
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun a _ => val_transferLetter E a)

/-- **A transported word has the length of the original.**  The side count of the
polygon the estimate is applied to is read off this. -/
theorem length_map_transferLetter (E : Subgroup G) (w : List (RelLetter G Λ)) :
    (w.map (transferLetter E)).length = w.length :=
  List.length_map _

/-- **A transported word traces the same path.**  `vertex` advances by `a.val` at
each step, and `val_transferLetter` says that is unchanged, so the two words have
the same vertices --- which is what lets isolation, a statement about vertices,
be read on either side. -/
theorem vertex_map_transferLetter (E : Subgroup G) :
    ∀ (w : List (RelLetter G Λ)) (v : G) (i : ℕ),
      OsinComponents.vertex v (w.map (transferLetter E)) i
        = OsinComponents.vertex v w i := by
  intro w
  induction w with
  | nil =>
      intro v i
      cases i <;> rfl
  | cons a t ih =>
      intro v i
      cases i with
      | zero => rfl
      | succ j =>
          show OsinComponents.vertex (v * (transferLetter E a).val)
              (t.map (transferLetter E)) j
            = OsinComponents.vertex (v * a.val) t j
          rw [val_transferLetter, ih]

/-! ## 3.  Admissible letters stay admissible -/

/-- **The translation lands in `D_E`.**

Each of the three cases checks against a different part of `D_E`: a letter of
`E` against its family, a remaining base letter against `X ⊆ X ∪ ⋃H_λ`, and a
peripheral letter against `⋃H_λ ⊆ X ∪ ⋃H_λ`.  The middle case is where the
classical choice pays off --- a base letter that is not in `E` must have come
from `X`, since the enlargement's base is exactly `X ∪ E`. -/
theorem isLetter_transferLetter {D : RelGenSet G Λ} {E : Subgroup G}
    {DE : RelGenSet G Unit} (hbase : DE.base = D.alphabet.carrier)
    (hfam : DE.fam = fun _ => E) {a : RelLetter G Λ}
    (ha : (relGenSetAddSubgroup D E).IsLetter a) :
    DE.IsLetter (transferLetter E a) := by
  cases a with
  | base x =>
      by_cases hx : x ∈ E
      · rw [transferLetter_base_of_mem hx]
        show x ∈ DE.fam ()
        rw [hfam]
        exact hx
      · rw [transferLetter_base_of_notMem hx]
        show x ∈ DE.base
        rw [hbase]
        rcases ha with hX | hE
        · exact Set.mem_union_left _ hX
        · exact absurd (SetLike.mem_coe.mp hE) hx
  | comp lam h =>
      show h ∈ DE.base
      rw [hbase]
      refine Set.mem_union_right _ ?_
      exact Set.mem_iUnion.mpr ⟨lam, SetLike.mem_coe.mpr ha⟩

/-! ## 4.  The `E`-letters are exactly the components -/

/-- **An `E`-letter becomes a component.**  This is the direction the estimate
consumes: it bounds isolated components, so every letter that must be bounded has
to have become one. -/
theorem isCompOf_transferLetter_base_of_mem {E : Subgroup G} {x : G}
    (hx : x ∈ E) :
    (transferLetter (Λ := Λ) E (RelLetter.base x)).IsCompOf () := by
  rw [transferLetter_base_of_mem hx]
  rfl

/-- **Nothing else does.**  A base letter outside `E` stays a base letter, and
`IsCompOf` is `False` at a base letter. -/
theorem not_isCompOf_transferLetter_base_of_notMem {E : Subgroup G} {x : G}
    (hx : x ∉ E) :
    ¬ (transferLetter (Λ := Λ) E (RelLetter.base x)).IsCompOf () := by
  rw [transferLetter_base_of_notMem hx]
  exact id

/-- A peripheral letter becomes a base letter, so it is not a component either.
Together with the previous two this pins the components of the transported word
exactly: they are the positions carrying an element of `E`. -/
theorem not_isCompOf_transferLetter_comp (E : Subgroup G) (lam : Λ) (h : G) :
    ¬ (transferLetter E (RelLetter.comp lam h)).IsCompOf () := id

end Transfer

end GGT
end GroupApproximation
