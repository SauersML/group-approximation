import GroupApproximation.Higman.NormalClosureProduct
import GroupApproximation.Higman.BlockWordProblem

/-!
# The word problem of a presented group, as relator data

Every recursive-presentation argument in this lane has so far been done by
hand: `Higman.BlockComputable` for the coded direct sum, `Higman.TowerComputable`
for the torsion-free radical.  Input (4) of `Higman.FinalReduction`,
`BridgeRecursive`, is a third instance, and there is a general tool underneath
all of them:

> if a group is presented on a computable generating family by a recursively
> enumerable set of relators, its word problem is recursively enumerable.

This file is the algebraic half of that tool, which is all that can be stated
without fixing how the relator set is enumerated.  A raw word dies in the group
exactly when its value in the *free* group is a product of conjugates of
relators --- and in the free group everything in sight is decidable, so the
resulting search has a decidable matrix.

## The two halves

* **Here.**  `evalRaw_eq_one_iff_conjProd`: triviality is a finite list of
  conjugation data, by `Higman.mem_normalClosure_iff_conjProd`.  The relator
  set has to be symmetric, which costs nothing: the normal closure of `S` is
  the normal closure of `S ∪ S⁻¹`, and `symmetrize` below makes that explicit.
* **Not here.**  That the search is computable.  That needs the relator set in
  certificate form --- `∃ n, check r n = true` with `check` computable --- and
  the free-group equation discharged by the repository's deletion certificates
  (`Computability.CodedWordTriviality`), exactly as
  `WordProblemRE.searchCheck` does for a single finite presentation.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes

variable {A : Type} [Group A]

/-! ## 1.  Symmetrizing the relator set -/

/-- A relator set together with the inverses of its members.  The normal
closure is unchanged, and the result is symmetric, which is what
`mem_normalClosure_iff_conjProd` asks for. -/
def symmetrize {G : Type} [Group G] (S : Set G) : Set G := S ∪ (fun x ↦ x⁻¹) '' S

theorem subset_symmetrize {G : Type} [Group G] (S : Set G) : S ⊆ symmetrize S :=
  Set.subset_union_left

theorem symmetrize_symm {G : Type} [Group G] (S : Set G) :
    ∀ x ∈ symmetrize S, x⁻¹ ∈ symmetrize S := by
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact Or.inr ⟨x, hx, rfl⟩
  · simpa only [inv_inv] using subset_symmetrize S hy

theorem normalClosure_symmetrize {G : Type} [Group G] (S : Set G) :
    Subgroup.normalClosure (symmetrize S) = Subgroup.normalClosure S := by
  refine le_antisymm ?_ (Subgroup.normalClosure_le_normal
    (Set.Subset.trans (subset_symmetrize S) Subgroup.subset_normalClosure))
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact Subgroup.subset_normalClosure hx
  · exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure hy)

/-! ## 2.  Triviality as conjugation data -/

/-- The value of a raw word in the free group on the generating indices. -/
def freeEval (w : RawWord) : FreeGroup ℕ := evalRaw FreeGroup.of w

theorem freeEval_eq (w : RawWord) :
    freeEval w = FreeGroup.mk (w.map fun p ↦ (p.1, p.2)) := by
  show evalRaw (fun k ↦ FreeGroup.of k) w = _
  rw [evalRaw_freeGroup]

/-- **The word problem, as relator data.**  If the group is presented on `gen`
by the relators `S`, then a raw word dies exactly when its free value is a
finite product of conjugates of relators.

Everything on the right-hand side lives in the free group, where equality is
decidable; the only recursively enumerable ingredient is membership in `S`. -/
theorem evalRaw_eq_one_iff_conjProd (gen : ℕ → A) (S : Set (FreeGroup ℕ))
    (hpres : ∀ w : RawWord,
      evalRaw gen w = 1 ↔ freeEval w ∈ Subgroup.normalClosure S)
    (w : RawWord) :
    evalRaw gen w = 1 ↔
      ∃ l : List (FreeGroup ℕ × FreeGroup ℕ),
        (∀ p ∈ l, p.2 ∈ symmetrize S) ∧ conjProd l = freeEval w := by
  rw [hpres w, ← normalClosure_symmetrize S]
  exact mem_normalClosure_iff_conjProd (symmetrize_symm S) (freeEval w)

/-- The same, with the conjugation data given by raw words.  This is the form
a certificate carries: the conjugators and the relators are both words in the
generating indices, so the whole witness is `Primcodable` data. -/
theorem evalRaw_eq_one_iff_raw (gen : ℕ → A) (S : Set (FreeGroup ℕ))
    (hpres : ∀ w : RawWord,
      evalRaw gen w = 1 ↔ freeEval w ∈ Subgroup.normalClosure S)
    (w : RawWord) :
    evalRaw gen w = 1 ↔
      ∃ l : List (RawWord × RawWord),
        (∀ p ∈ l, freeEval p.2 ∈ symmetrize S) ∧
          conjProd (l.map fun p ↦ (freeEval p.1, freeEval p.2)) = freeEval w := by
  rw [evalRaw_eq_one_iff_conjProd gen S hpres w]
  constructor
  · rintro ⟨l, hl, heq⟩
    classical
    have hword : ∀ x : FreeGroup ℕ, ∃ v : RawWord, freeEval v = x := by
      intro x
      refine (mem_closure_iff_exists_evalRaw FreeGroup.of x).1 ?_
      rw [FreeGroup.closure_range_of]
      exact Subgroup.mem_top x
    let wordOfFree (x : FreeGroup ℕ) : RawWord := Classical.choose (hword x)
    have wordOfFree_spec (x : FreeGroup ℕ) : freeEval (wordOfFree x) = x :=
      Classical.choose_spec (hword x)
    refine ⟨l.map (fun p ↦ (wordOfFree p.1, wordOfFree p.2)), ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      rw [wordOfFree_spec]
      exact hl p hp
    · have hlist :
          (l.map (fun p ↦ (wordOfFree p.1, wordOfFree p.2))).map
              (fun q ↦ (freeEval q.1, freeEval q.2))
          = l := by
        rw [List.map_map]
        calc
          List.map
              ((fun q ↦ (freeEval q.1, freeEval q.2)) ∘
                fun p ↦ (wordOfFree p.1, wordOfFree p.2)) l =
              List.map id l := List.map_congr_left fun p _ =>
                Prod.ext (wordOfFree_spec p.1) (wordOfFree_spec p.2)
          _ = l := List.map_id l
      rw [hlist, heq]
  · rintro ⟨l, hl, heq⟩
    exact ⟨l.map fun p ↦ (freeEval p.1, freeEval p.2),
      fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hl q hq,
      heq⟩

end Higman
end GroupApproximation
