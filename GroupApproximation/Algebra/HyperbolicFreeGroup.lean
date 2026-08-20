import GroupApproximation.Algebra.TreeLikeHyperbolic
import GroupApproximation.Algebra.ListCommonPrefix
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Free groups are `0`-hyperbolic

Before this module the library could exhibit exactly three hyperbolic groups:
finite ones (bounded word metric), the trivial group, and `Multiplicative ℤ`.
All three are elementary, so `IsHyperbolicGroup` had no witness that a
hyperbolic group can be large.  This module supplies the first nonelementary
one: **a free group on a finite basis is `0`-hyperbolic**.

## The proof

`Algebra/TreeLikeHyperbolic.lean` reduces the four-point condition at `δ = 0` to
a *common prefix length* `p` with

```
    d_S(x,y) + 2 p x y = |x|_S + |y|_S      and      min (p x z) (p y z) ≤ p x y.
```

For a free group take `p x y` to be the length of the longest common prefix of
the reduced words of `x` and `y` (`ListPrefix.lcp`).  The ultrametric axiom is
then `ListPrefix.lcp_ultra`, pure list combinatorics.  The cancellation axiom is
the content:

* `wordNorm_freeAlphabet` identifies the repository's word length over the
  alphabet `{x_a, x_a⁻¹}` with Mathlib's `FreeGroup.norm`, the length of the
  reduced word.  One direction spells an element by its own reduced word; the
  other bounds `norm` along a product by `FreeGroup.norm_mul_le`.
* `norm_inv_mul_add_two_mul_lcp` is the cancellation identity.  Writing
  `u = x.toWord`, `v = y.toWord` and `k = lcp u v`, the element `x⁻¹y` is
  `mk (invRev (drop k u) ++ drop k v)` --- the shared prefix cancels --- and
  that word is **reduced**, because past the common prefix the two words
  disagree (`ListPrefix.lcp_drop_ne`), so the junction letter of the
  concatenation is not the formal inverse of its neighbour.  Hence
  `norm (x⁻¹y) = (|u| - k) + (|v| - k)`.

The reducedness step is `isReduced_invRev_append`, and it is where the tree
shows up: it is exactly the statement that the geodesics from `1` to `x` and
from `1` to `y` separate once and never meet again.

## What this is for

`Kazhdan/SharpExistenceCertificateRoute.lean` reduces `SharpExistence` to a
concrete group that is infinite, finitely presented, torsion-free and hyperbolic
together with a rational Hodge certificate.  A free group supplies the first
four clauses and fails only the certificate --- necessarily, since a free group
does not have property `(T)`.  What it contributes is the hyperbolicity
machinery: `IsTreeLike` and this instantiation are the base case for the
small-cancellation and Bass--Serre arguments that a genuine witness would need.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric
open ListPrefix

variable {α : Type} [DecidableEq α]

/-! ## The alphabet -/

/-- The group element named by a letter of a reduced word. -/
def letterOf : α × Bool → FreeGroup α
  | (a, true) => FreeGroup.of a
  | (a, false) => (FreeGroup.of a)⁻¹

/-- The generating alphabet of a free group: the basis and its inverses. -/
def freeAlphabet (α : Type) [DecidableEq α] : Set (FreeGroup α) :=
  Set.range (letterOf (α := α))

theorem letterOf_mem (w : α × Bool) : letterOf w ∈ freeAlphabet α := ⟨w, rfl⟩

omit [DecidableEq α] in
/-- A one-letter word is its letter. -/
theorem mk_singleton_letterOf (w : α × Bool) :
    FreeGroup.mk [w] = letterOf w := by
  obtain ⟨a, b⟩ := w
  cases b <;> rfl

omit [DecidableEq α] in
/-- Inverting a letter flips its exponent. -/
theorem inv_letterOf (w : α × Bool) :
    (letterOf w)⁻¹ = letterOf (w.1, !w.2) := by
  obtain ⟨a, b⟩ := w
  cases b
  · show ((FreeGroup.of a)⁻¹)⁻¹ = FreeGroup.of a
    rw [inv_inv]
  · rfl

/-- Every letter has reduced length one. -/
theorem norm_letterOf (w : α × Bool) : FreeGroup.norm (letterOf w) = 1 := by
  obtain ⟨a, b⟩ := w
  cases b
  · show FreeGroup.norm (FreeGroup.of a)⁻¹ = 1
    rw [FreeGroup.norm_inv_eq, FreeGroup.norm_of]
  · exact FreeGroup.norm_of a

omit [DecidableEq α] in
/-- Spelling a word out letter by letter recovers the element it presents. -/
theorem prod_map_letterOf (L : List (α × Bool)) :
    (L.map letterOf).prod = FreeGroup.mk L := by
  induction L with
  | nil => simp [FreeGroup.one_eq_mk]
  | cons w L ih =>
    rw [List.map_cons, List.prod_cons, ih, ← mk_singleton_letterOf,
      FreeGroup.mul_mk]
    rfl

/-- **The alphabet is a symmetric generating set.** -/
theorem isSymmetricGeneratingSet_freeAlphabet :
    IsSymmetricGeneratingSet (freeAlphabet α) := by
  refine ⟨?_, ?_⟩
  · rintro z ⟨w, rfl⟩
    exact ⟨(w.1, !w.2), (inv_letterOf w).symm⟩
  · refine top_le_iff.mp ?_
    rw [← FreeGroup.closure_range_of α]
    refine Subgroup.closure_mono ?_
    rintro z ⟨a, rfl⟩
    exact ⟨(a, true), rfl⟩

/-! ## The word length is the reduced length -/

/-- Reduced length is subadditive along a list of letters. -/
theorem norm_prod_le (l : List (FreeGroup α))
    (h : ∀ z ∈ l, FreeGroup.norm z ≤ 1) :
    FreeGroup.norm l.prod ≤ l.length := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hz : FreeGroup.norm z ≤ 1 := h z (by simp)
    have hl : FreeGroup.norm l.prod ≤ l.length :=
      ih fun w hw => h w (by simp [hw])
    have hmul := FreeGroup.norm_mul_le z l.prod
    rw [List.prod_cons]
    simp only [List.length_cons]
    omega

/-- **The word metric of a free group is the reduced word length.** -/
theorem wordNorm_freeAlphabet (g : FreeGroup α) :
    wordNorm (freeAlphabet α) g = FreeGroup.norm g := by
  refine le_antisymm ?_ ?_
  · have hw : IsWord (freeAlphabet α) (g.toWord.map letterOf) g := by
      refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
        exact letterOf_mem w
      · rw [prod_map_letterOf, FreeGroup.mk_toWord]
    have hle := wordNorm_le_length hw
    simpa [FreeGroup.norm] using hle
  · obtain ⟨l, hl, hlen⟩ :=
      exists_isWord_length_eq isSymmetricGeneratingSet_freeAlphabet g
    have hb : ∀ z ∈ l, FreeGroup.norm z ≤ 1 := by
      intro z hz
      obtain ⟨w, rfl⟩ := hl.letters z hz
      exact le_of_eq (norm_letterOf w)
    have hp := norm_prod_le l hb
    rw [hl.prod_eq] at hp
    omega

/-! ## Cancellation past the common prefix -/

omit [DecidableEq α] in
/-- Tails of reduced words are reduced. -/
theorem isReduced_drop {L : List (α × Bool)} (h : FreeGroup.IsReduced L) (n : ℕ) :
    FreeGroup.IsReduced (List.drop n L) := by
  have hsplit : List.take n L ++ List.drop n L = L := List.take_append_drop n L
  rw [← hsplit] at h
  exact List.IsChain.right_of_append h

/-- Formally inverting a reduced word keeps it reduced. -/
theorem isReduced_invRev {L : List (α × Bool)} (h : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (FreeGroup.invRev L) := by
  rw [FreeGroup.isReduced_iff_reduce_eq, FreeGroup.reduce_invRev, h.reduce_eq]

/-- **The junction case.**  If two reduced words start with letters that are not
equal, then the formal inverse of the first, concatenated with the second, is
reduced: the only place a cancellation could occur is at the junction, and there
it would force the two leading letters to agree. -/
theorem isReduced_invRev_append_cons {A' B' : List (α × Bool)} {a b : α × Bool}
    (hA : FreeGroup.IsReduced (a :: A')) (hB : FreeGroup.IsReduced (b :: B'))
    (hab : a.1 = b.1 → a.2 ≠ b.2) :
    FreeGroup.IsReduced (FreeGroup.invRev (a :: A') ++ (b :: B')) := by
  have hinvA : FreeGroup.IsReduced (FreeGroup.invRev (a :: A')) := isReduced_invRev hA
  obtain ⟨a1, a2⟩ := a
  have hinv : FreeGroup.invRev ((a1, a2) :: A')
      = FreeGroup.invRev A' ++ [(a1, !a2)] := by
    rw [FreeGroup.invRev_cons]
    rfl
  rw [hinv] at hinvA ⊢
  rw [List.append_assoc]
  show List.IsChain (fun p q : α × Bool ↦ p.1 = q.1 → p.2 = q.2)
    (FreeGroup.invRev A' ++ (a1, !a2) :: b :: B')
  rw [List.isChain_append_cons_cons]
  refine ⟨hinvA, ?_, hB⟩
  intro hfst
  have hne : a2 ≠ b.2 := hab hfst
  have hbool : ∀ s t : Bool, s ≠ t → (!s) = t := by decide
  exact hbool a2 b.2 hne

/-- The general form: `invRev A ++ B` is reduced whenever `A` and `B` are and
their leading letters differ. -/
theorem isReduced_invRev_append {A B : List (α × Bool)}
    (hA : FreeGroup.IsReduced A) (hB : FreeGroup.IsReduced B)
    (hab : ∀ (a : α × Bool) (A' : List (α × Bool)), A = a :: A' →
      ∀ (b : α × Bool) (B' : List (α × Bool)), B = b :: B' →
        a.1 = b.1 → a.2 ≠ b.2) :
    FreeGroup.IsReduced (FreeGroup.invRev A ++ B) := by
  cases A with
  | nil => simpa using hB
  | cons a A' =>
    cases B with
    | nil => simpa using isReduced_invRev hA
    | cons b B' => exact isReduced_invRev_append_cons hA hB (hab a A' rfl b B' rfl)

omit [DecidableEq α] in
/-- Splitting an element at a prefix of its reduced word. -/
theorem inv_mk_mul_mk_eq {u v : List (α × Bool)} {k : ℕ}
    (htake : List.take k u = List.take k v) :
    (FreeGroup.mk u)⁻¹ * FreeGroup.mk v
      = FreeGroup.mk (FreeGroup.invRev (List.drop k u) ++ List.drop k v) := by
  have hu : FreeGroup.mk u
      = FreeGroup.mk (List.take k u) * FreeGroup.mk (List.drop k u) := by
    rw [FreeGroup.mul_mk, List.take_append_drop]
  have hv : FreeGroup.mk v
      = FreeGroup.mk (List.take k u) * FreeGroup.mk (List.drop k v) := by
    rw [FreeGroup.mul_mk, htake, List.take_append_drop]
  rw [hu, hv, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  group

/-- **The cancellation identity.**  The reduced word of `x⁻¹y` is what is left
of the reduced words of `x` and `y` once their common prefix is removed. -/
theorem norm_inv_mul_add_two_mul_lcp (x y : FreeGroup α) :
    FreeGroup.norm (x⁻¹ * y) + 2 * lcp x.toWord y.toWord
      = FreeGroup.norm x + FreeGroup.norm y := by
  classical
  have hku : lcp x.toWord y.toWord ≤ x.toWord.length := lcp_le_length_left _ _
  have hkv : lcp x.toWord y.toWord ≤ y.toWord.length := lcp_le_length_right _ _
  have htake : List.take (lcp x.toWord y.toWord) x.toWord
      = List.take (lcp x.toWord y.toWord) y.toWord := take_lcp_left_eq_right _ _
  have hdu : FreeGroup.IsReduced (List.drop (lcp x.toWord y.toWord) x.toWord) :=
    isReduced_drop FreeGroup.isReduced_toWord _
  have hdv : FreeGroup.IsReduced (List.drop (lcp x.toWord y.toWord) y.toWord) :=
    isReduced_drop FreeGroup.isReduced_toWord _
  have hred : FreeGroup.IsReduced
      (FreeGroup.invRev (List.drop (lcp x.toWord y.toWord) x.toWord)
        ++ List.drop (lcp x.toWord y.toWord) y.toWord) := by
    refine isReduced_invRev_append hdu hdv ?_
    intro a A' hA b B' hB hfst hsnd
    refine lcp_drop_ne x.toWord y.toWord hA hB ?_
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp_all
  have heq : x⁻¹ * y = FreeGroup.mk
      (FreeGroup.invRev (List.drop (lcp x.toWord y.toWord) x.toWord)
        ++ List.drop (lcp x.toWord y.toWord) y.toWord) := by
    have h := inv_mk_mul_mk_eq (u := x.toWord) (v := y.toWord)
      (k := lcp x.toWord y.toWord) htake
    rwa [FreeGroup.mk_toWord, FreeGroup.mk_toWord] at h
  have hword : (x⁻¹ * y).toWord
      = FreeGroup.invRev (List.drop (lcp x.toWord y.toWord) x.toWord)
        ++ List.drop (lcp x.toWord y.toWord) y.toWord := by
    rw [heq, FreeGroup.toWord_mk, hred.reduce_eq]
  simp only [FreeGroup.norm, hword, List.length_append, FreeGroup.invRev_length,
    List.length_drop]
  omega

/-! ## Free groups are `0`-hyperbolic -/

/-- **A free group is tree-like** over its basis alphabet, with the length of
the longest common prefix of reduced words as the prefix function. -/
theorem isTreeLike_freeAlphabet :
    IsTreeLike (freeAlphabet α) (fun x y => lcp x.toWord y.toWord) := by
  constructor
  · intro x y
    have hdist : wordDist (freeAlphabet α) x y = FreeGroup.norm (x⁻¹ * y) := by
      unfold wordDist
      exact wordNorm_freeAlphabet _
    rw [hdist, wordNorm_freeAlphabet, wordNorm_freeAlphabet]
    exact norm_inv_mul_add_two_mul_lcp x y
  · intro x y z
    exact lcp_ultra x.toWord y.toWord z.toWord

/-- The basis alphabet as a `Finset`, for a free group of finite rank. -/
def freeAlphabetFinset (α : Type) [Fintype α] [DecidableEq α] :
    Finset (FreeGroup α) :=
  Finset.image (letterOf (α := α)) (Finset.univ : Finset (α × Bool))

@[simp] theorem coe_freeAlphabetFinset (α : Type) [Fintype α] [DecidableEq α] :
    (freeAlphabetFinset α : Set (FreeGroup α)) = freeAlphabet α := by
  rw [freeAlphabetFinset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

/-- **A free group of finite rank is `0`-hyperbolic.**  The first nonelementary
hyperbolic group in this library: it is infinite as soon as the basis is
nonempty, torsion-free, and finitely presented, so it satisfies four of the five
clauses of `SharpExistence`.  It fails the fifth --- property `(T)` --- and must,
since a free group acts on a tree with unbounded orbits. -/
theorem isHyperbolicGroup_freeGroup (α : Type) [Fintype α] [DecidableEq α] :
    IsHyperbolicGroup (FreeGroup α) := by
  refine isHyperbolicGroup_of_isTreeLike (T := freeAlphabetFinset α) ?_
    (q := fun x y => lcp x.toWord y.toWord) ?_
  · rw [coe_freeAlphabetFinset]
    exact isSymmetricGeneratingSet_freeAlphabet
  · rw [coe_freeAlphabetFinset]
    exact isTreeLike_freeAlphabet

end Hyperbolic
end GroupApproximation
