import GroupApproximation.Higman.RadicalDirectSum
import GroupApproximation.Higman.TowerDerivation

/-!
# (B2) in raw-data form

Two reductions meet here.  `Higman.RadicalDirectSum` says the absorber's word
problem is, block by block, radical membership in one *finitely presented*
coded group; `Higman.TowerDerivation` says radical membership in any group with
a spanning family is `∃ i, TowerDeriv gen i v`, a recursion on raw words.
Composing them:

    evalRaw (quotientGen pcGen) w = 1
      ↔  ∀ c ∈ blockList w, ∃ i, TowerDeriv (generators of c) i (blockWord w c) .

Both sides are now raw data plus instances of the coded word problem, and the
list `blockList w` and the words `blockWord w c` are computed from `w` by
`List.map` and `List.filter`, whose primitive recursiveness is already proved in
`Higman.BlockComputable`.

The one new ingredient is that the coded group's generators, *indexed by* `ℕ`
through `PresentationCodes.letterOf`, still span: `letterOf c` is surjective
onto `Fin (genCount c)` because `genCount` is positive and `letterOf` reduces
mod it, which is `PresentationCodes.letterOf_val`.

## What (B2) still owes

One statement, and it no longer mentions groups:

    REPred fun w ↦ ∀ c ∈ blockList w, ∃ i, TowerDeriv (gen c) i (blockWord w c)

`TowerDeriv` is a recursion whose only non-raw content is the word problem of a
finite presentation, which is recursively enumerable
(`Computability.WordProblemRE.rePred_wordProblemPred`).  Making the whole thing
recursively enumerable is the flattening: a derivation is a list of claims, each
justified by earlier entries, checked against its own prefix, so that the search
is again one existential over a `Primcodable` type with a decidable matrix ---
the shape `WordProblemRE.rePred_exists_eq_true` consumes and the shape
`Higman.BlockSearch`/`Higman.BlockComputable` already used to finish (B1).
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo
open GroupApproximation.PresentationCodes

/-! ## 1.  The coded generators, indexed by `ℕ`, still span -/

theorem letterOf_surjective (c : PresentationCode) :
    Function.Surjective (letterOf c) := by
  intro j
  obtain ⟨m, l⟩ := c
  exact ⟨(j : ℕ), letterOf_val m l j⟩

theorem spans_codedGen (c : PresentationCode) :
    Subgroup.closure
        (Set.range fun k : ℕ ↦
          (PresentedGroup.of (letterOf c k) : Carrier c)) = ⊤ := by
  have hrange :
      (Set.range fun k : ℕ ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
        = Set.range (PresentedGroup.of : Fin (genCount c) → Carrier c) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨letterOf c k, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := letterOf_surjective c j
      exact ⟨k, congrArg PresentedGroup.of hk⟩
  rw [hrange, PresentedGroup.closure_range_of]

/-! ## 2.  The absorber's word problem, in raw-data form -/

/-- **(B2)'s predicate, with no groups left in it.** -/
theorem evalRaw_quotient_eq_one_iff_towerDeriv (w : RawWord) :
    evalRaw (quotientGen pcGen) w = 1 ↔
      ∀ c ∈ blockList w, ∃ i : ℕ,
        TowerDeriv (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c)) i
          (blockWord w c) := by
  rw [evalRaw_quotient_eq_one_iff_blocks]
  refine forall_congr' fun c => imp_congr_right fun _ => ?_
  exact mem_radical_iff_exists_towerDeriv _ (spans_codedGen c) _

/-- **(B2), reduced to a single recursive-enumerability statement about raw
words.**  Everything else in Chiodo's Proposition 3.8 is now proved. -/
noncomputable def recursivePresentationPCAbsorber'
    (hre : REPred fun w : RawWord ↦ ∀ c ∈ blockList w, ∃ i : ℕ,
      TowerDeriv (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c)) i
        (blockWord w c)) :
    RecursivePresentation PCAbsorber where
  gen := quotientGen pcGen
  spans := spans_quotientGen spans_pcGen
  re := hre.of_eq fun w ↦ (evalRaw_quotient_eq_one_iff_towerDeriv w).symm

end Higman
end GroupApproximation
