import GroupApproximation.Higman.BlockDecomposition
import GroupApproximation.Higman.QuotientPresentation

/-!
# The radical of the absorber is coordinatewise

`Higman.QuotientPresentation` reduces (B2) --- Chiodo Proposition 3.8 at the
absorber --- to recursive enumerability of

    { w | evalRaw pcGen w ∈ torsionFreeRadical PCDirectSum } .

That is a statement about an *infinitely generated* group, and it looks harder
than Chiodo's Proposition 3.8, which is about presentations one at a time.
This file shows it is not: the torsion-free radical of a restricted direct
product is the direct sum of the radicals, so the predicate is a conjunction,
over the finitely many blocks of `w`, of the *same* predicate for a single
**finitely presented** coded group.

Both inclusions are cheap.  One is functoriality of the radical
(`Chiodo.mem_torsionFreeRadical_map`, already proved: `ρ` is a subfunctor of
the identity), applied to the coordinate evaluation.  The other is the same
functoriality applied to the coordinate inclusion, together with the fact that
an element of a restricted direct product is a finite product of coordinate
elements --- `DFinsupp.induction`, exactly as in `Higman.CodedAbsorber`'s
`spans_pcGen`.

## Consequence

`PCAbsorber = PCDirectSum ᵗᶠ` is, coordinatewise, `⨁_c (Carrier c) ᵗᶠ`, and its
word problem is block by block the radical-membership problem of one finite
presentation.  So (B2) is Chiodo's Proposition 3.8 **for finitely presented
groups, uniformly in the code**, which is the form he states effectively, and
the block bookkeeping is the same as (B1)'s.

`recursivePresentationPCAbsorber` takes that one statement and returns the
recursive presentation of the absorber.  Nothing here proves it.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo
open GroupApproximation.PresentationCodes

/-! ## 1.  Functoriality at the coordinates -/

theorem pcEval_mem_radical (c : PresentationCode) {g : PCDirectSum}
    (hg : g ∈ torsionFreeRadical PCDirectSum) :
    pcEval c g ∈ torsionFreeRadical (Carrier c) :=
  mem_torsionFreeRadical_map (pcEval c) hg

theorem pcOf_mem_radical (c : PresentationCode) {x : Carrier c}
    (hx : x ∈ torsionFreeRadical (Carrier c)) :
    pcOf c x ∈ torsionFreeRadical PCDirectSum :=
  mem_torsionFreeRadical_map (pcOf c) hx

/-! ## 2.  The radical is coordinatewise -/

theorem mem_radical_of_coords :
    ∀ f : Π₀ c : PresentationCode, Additive (Carrier c),
      (∀ c, Additive.toMul (f c) ∈ torsionFreeRadical (Carrier c)) →
        (Multiplicative.ofAdd f : PCDirectSum) ∈
          torsionFreeRadical PCDirectSum := by
  classical
  intro f
  refine DFinsupp.induction
    (p := fun f : Π₀ c : PresentationCode, Additive (Carrier c) ↦
      (∀ c, Additive.toMul (f c) ∈ torsionFreeRadical (Carrier c)) →
        (Multiplicative.ofAdd f : PCDirectSum) ∈
          torsionFreeRadical PCDirectSum) f ?_ ?_
  · intro _
    change (1 : PCDirectSum) ∈ torsionFreeRadical PCDirectSum
    exact Subgroup.one_mem _
  · intro c a f' hf' _ ih hcoord
    have hca : Additive.toMul a ∈ torsionFreeRadical (Carrier c) := by
      have h := hcoord c
      simpa [DFinsupp.add_apply, hf'] using h
    have hrest : ∀ d, Additive.toMul (f' d) ∈ torsionFreeRadical (Carrier d) := by
      intro d
      by_cases hd : d = c
      · subst d
        rw [hf']
        change (1 : Carrier c) ∈ torsionFreeRadical (Carrier c)
        exact Subgroup.one_mem _
      · have h := hcoord d
        simpa [DFinsupp.add_apply, hd, Ne.symm hd] using h
    have ha : (Multiplicative.ofAdd (DFinsupp.single c a) : PCDirectSum) =
        pcOf c (Additive.toMul a) := by
      apply Multiplicative.ofAdd.injective
      simp [pcOf]
    let tail : PCDirectSum := Multiplicative.ofAdd f'
    have hm : pcOf c (Additive.toMul a) * tail ∈ torsionFreeRadical PCDirectSum :=
      Subgroup.mul_mem _ (pcOf_mem_radical c hca) (ih hrest)
    simp only [tail] at hm
    rw [← ha] at hm
    exact hm

/-- **The radical of a restricted direct product is coordinatewise.** -/
theorem mem_radical_iff_coords (g : PCDirectSum) :
    g ∈ torsionFreeRadical PCDirectSum ↔
      ∀ c : PresentationCode, pcEval c g ∈ torsionFreeRadical (Carrier c) := by
  constructor
  · intro hg c
    exact pcEval_mem_radical c hg
  · intro h
    exact mem_radical_of_coords (Multiplicative.toAdd g) h

/-! ## 3.  Block by block -/

/-- The `c`-coordinate of a raw word's value is the value of its block-`c`
subword at the coded group's own generators.  This is the chain
`map_evalRaw` → `evalRaw_filter` → `evalRaw_reindex`, packaged. -/
theorem pcEval_evalRaw_pcGen (c : PresentationCode) (w : RawWord) :
    pcEval c (evalRaw pcGen w)
      = evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
          (blockWord w c) := by
  have hv : ∀ p ∈ (w.filter fun p ↦ decide (blockOf p.1 = c)),
      blockOf p.1 = c := by
    intro p hp
    simpa using (List.mem_filter.1 hp).2
  have hfil : evalRaw (fun n ↦ pcEval c (pcGen n))
      (w.filter fun p ↦ decide (blockOf p.1 = c))
      = evalRaw (fun n ↦ pcEval c (pcGen n)) w := by
    refine evalRaw_filter _ _ w ?_
    intro p _ hp
    exact pcEval_pcGen_of_ne (by simpa using hp)
  rw [map_evalRaw, ← hfil]
  exact evalRaw_reindex c _ hv

/-- **Radical membership is block by block.** -/
theorem evalRaw_pcGen_mem_radical_iff (w : RawWord) :
    evalRaw pcGen w ∈ torsionFreeRadical PCDirectSum ↔
      ∀ c ∈ blockList w,
        evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
          (blockWord w c) ∈ torsionFreeRadical (Carrier c) := by
  rw [mem_radical_iff_coords]
  constructor
  · intro h c _
    rw [← pcEval_evalRaw_pcGen]
    exact h c
  · intro h c
    by_cases hc : c ∈ blockList w
    · rw [pcEval_evalRaw_pcGen]
      exact h c hc
    · have h1 : pcEval c (evalRaw pcGen w) = 1 := by
        rw [map_evalRaw]
        refine evalRaw_eq_one_of_letters _ _ ?_
        intro p hp
        refine pcEval_pcGen_of_ne ?_
        intro hEq
        exact hc (List.mem_map.2 ⟨p, hp, hEq⟩)
      rw [h1]
      exact Subgroup.one_mem _

/-! ## 4.  (B2), in its sharpest form -/

/-- **The word problem of the absorber, block by block.**  A raw word dies in
`PCAbsorber` exactly when, for each of the finitely many codes occurring as a
block of `w`, the block subword lies in the torsion-free radical of that
code's *finitely presented* group. -/
theorem evalRaw_quotient_eq_one_iff_blocks (w : RawWord) :
    evalRaw (quotientGen pcGen) w = 1 ↔
      ∀ c ∈ blockList w,
        evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
          (blockWord w c) ∈ torsionFreeRadical (Carrier c) := by
  rw [evalRaw_quotientGen_eq_one_iff, evalRaw_pcGen_mem_radical_iff]

/-- **(B2) reduced to one statement about finite presentations.**  Given that
the block-by-block radical-membership predicate is recursively enumerable, the
absorber is recursively presented.

This is Chiodo's Proposition 3.8 uniformly in the code, and it is all that
remains of (B2). -/
noncomputable def recursivePresentationPCAbsorber
    (hre : REPred fun w : RawWord ↦ ∀ c ∈ blockList w,
      evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
        (blockWord w c) ∈ torsionFreeRadical (Carrier c)) :
    RecursivePresentation PCAbsorber where
  gen := quotientGen pcGen
  spans := spans_quotientGen spans_pcGen
  re := hre.of_eq fun w ↦ (evalRaw_quotient_eq_one_iff_blocks w).symm

end Higman
end GroupApproximation
