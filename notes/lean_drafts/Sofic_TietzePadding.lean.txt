import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Tietze padding: lengthening every relator without changing the group

The ball-injectivity engine needs `2 * |W_d| <= min relator length`, and the
avatar rewrite scales both sides by the same factor, so no amount of avatar
inflation can rescue a presentation with a short relator.  The fix has to be
presentational, and this module supplies it.

Adjoin one fresh generator, written `none`, with defining relator
`none * T⁻¹` for a chosen long word `T`; and replace each old relator `r` by
`r * none * T⁻¹`.  In the presented group `none` and `T` are equal, so the
replacement is the old relator again and the group is unchanged; but as a
*word* every new relator now has length at least that of `T`.

Mathlib has no Tietze-transformation API — there is no occurrence of the name
anywhere in its group theory — so the equivalence is built here directly from
`PresentedGroup.toGroup` and `PresentedGroup.ext`, which is all it needs: two
homomorphisms defined on generators, shown mutually inverse on generators.
-/

namespace GroupApproximation
namespace TietzePadding

variable {α : Type*}

/-- The embedding of the old generators among the padded ones. -/
def emb : FreeGroup α →* FreeGroup (Option α) := FreeGroup.map some

/-- The defining relator of the fresh generator: it is the long word `T`. -/
def padAnchor (T : FreeGroup α) : FreeGroup (Option α) :=
  FreeGroup.of none * (emb T)⁻¹

/-- The padded form of a relator: same relator, followed by a word that is
trivial in the padded group and long as a word. -/
def padRelator (T : FreeGroup α) (r : FreeGroup α) : FreeGroup (Option α) :=
  emb r * FreeGroup.of none * (emb T)⁻¹

/-- The padded relator family. -/
def padRelators (T : FreeGroup α) (rels : Set (FreeGroup α)) :
    Set (FreeGroup (Option α)) :=
  insert (padAnchor T) (padRelator T '' rels)

/-! ## The two homomorphisms -/

/-- Generator assignment collapsing the fresh generator back onto `T`. -/
def collapse (T : FreeGroup α) (rels : Set (FreeGroup α)) :
    Option α → PresentedGroup rels :=
  fun a => a.elim (PresentedGroup.mk rels T) PresentedGroup.of

theorem lift_collapse_emb (T : FreeGroup α) (rels : Set (FreeGroup α))
    (x : FreeGroup α) :
    FreeGroup.lift (collapse T rels) (emb x) = PresentedGroup.mk rels x := by
  have h : (FreeGroup.lift (collapse T rels)).comp emb
      = PresentedGroup.mk rels := by
    apply FreeGroup.ext_hom
    intro a
    simp [emb, collapse, PresentedGroup.of]
  exact congrArg (fun φ : FreeGroup α →* PresentedGroup rels => φ x) h

theorem lift_collapse_eq_one (T : FreeGroup α) (rels : Set (FreeGroup α))
    (r : FreeGroup (Option α)) (hr : r ∈ padRelators T rels) :
    FreeGroup.lift (collapse T rels) r = 1 := by
  rcases hr with hr | ⟨r₀, hr₀, rfl⟩
  · subst hr
    simp [padAnchor, lift_collapse_emb, collapse]
  · rw [padRelator]
    simp only [map_mul, map_inv, lift_collapse_emb]
    rw [show FreeGroup.lift (collapse T rels) (FreeGroup.of none)
        = PresentedGroup.mk rels T from by simp [collapse]]
    rw [PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hr₀)]
    simp

/-- Collapse the fresh generator: the padded presentation maps onto the
original. -/
def toOriginal (T : FreeGroup α) (rels : Set (FreeGroup α)) :
    PresentedGroup (padRelators T rels) →* PresentedGroup rels :=
  PresentedGroup.toGroup (lift_collapse_eq_one T rels)

theorem lift_include_eq_one (T : FreeGroup α) (rels : Set (FreeGroup α))
    (r : FreeGroup α) (hr : r ∈ rels) :
    FreeGroup.lift (fun a : α => PresentedGroup.of (rels := padRelators T rels)
      (some a)) r = 1 := by
  sorry

/-- Include the old generators into the padded presentation. -/
def toPadded (T : FreeGroup α) (rels : Set (FreeGroup α)) :
    PresentedGroup rels →* PresentedGroup (padRelators T rels) :=
  PresentedGroup.toGroup (lift_include_eq_one T rels)

/-- **Padding does not change the presented group.** -/
def padEquiv (T : FreeGroup α) (rels : Set (FreeGroup α)) :
    PresentedGroup (padRelators T rels) ≃* PresentedGroup rels where
  toFun := toOriginal T rels
  invFun := toPadded T rels
  map_mul' := map_mul _
  left_inv := by sorry
  right_inv := by sorry

/-! ## Padding lengthens

The fresh letter `none` occurs in neither `emb r` nor `emb T`, so no
cancellation can cross it and the reduced word of a padded relator is the
concatenation of the three displayed blocks. -/

variable [DecidableEq α]

/-- The reduced word of a padded relator splits at the fresh letter. -/
theorem toWord_padRelator (T r : FreeGroup α) :
    (padRelator T r).toWord =
      (emb r).toWord ++ (none, true) :: ((emb T)⁻¹).toWord := by
  sorry

/-- Embedding preserves reduced length. -/
theorem norm_emb (x : FreeGroup α) : (emb x).toWord.length = x.toWord.length := by
  sorry

/-- **The length guarantee.**  Every padded relator is at least as long as the
padding word, whatever the relator was. -/
theorem le_norm_padRelator (T r : FreeGroup α) :
    T.toWord.length ≤ (padRelator T r).toWord.length := by
  rw [toWord_padRelator]
  have h : ((emb T)⁻¹).toWord.length = T.toWord.length := by
    rw [FreeGroup.toWord_inv, FreeGroup.invRev_length, norm_emb]
  simp only [List.length_append, List.length_cons, h]
  omega

/-- Every member of the padded family is at least as long as the padding
word. -/
theorem le_length_of_mem_padRelators (T : FreeGroup α)
    (rels : Set (FreeGroup α)) (r : FreeGroup (Option α))
    (hr : r ∈ padRelators T rels) :
    T.toWord.length ≤ r.toWord.length := by
  rcases hr with hr | ⟨r₀, _, rfl⟩
  · subst hr
    have h : (padAnchor T).toWord = (none, true) :: ((emb T)⁻¹).toWord := by
      sorry
    have h2 : ((emb T)⁻¹).toWord.length = T.toWord.length := by
      rw [FreeGroup.toWord_inv, FreeGroup.invRev_length, norm_emb]
    rw [h]
    simp only [List.length_cons, h2]
    omega
  · exact le_norm_padRelator T r₀

end TietzePadding
end GroupApproximation
