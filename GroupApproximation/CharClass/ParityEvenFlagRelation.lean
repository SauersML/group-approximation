import GroupApproximation.CharClass.ParityEvenSplitting
import GroupApproximation.CharClass.SplitRelationRange
import GroupApproximation.CharClass.CohomologyTotalNontrivial

/-!
# `Wu.HasSplitting` for a bundle over a compact base, unconditionally

`ParityEvenSplitting.lean` reduced the splitting datum to one input, the split
relation for the pullback of the bundle to the top stage of its flag tower.  This
file discharges that input from the geometry already on `origin/main` and so
removes the last hypothesis: over a compact non-empty base a bundle of constant
positive rank *has* a splitting, with no further obligation of any kind.

## The three ingredients

* `Bundle.flag_decomposition` — on the top stage the pullback is the sum of the
  tautological lines.  This is the trace argument, and it is the only place the
  rank hypothesis is used.
* `SplitRelationRange.splitRelation_of_sum_lt` — the split relation from such a
  decomposition, with the trace hypothesis restricted to the range.  The
  restriction is not a convenience here: `Bundle.flagLine p r l` is *zero* for
  `l ≥ r`, so the unrestricted hypothesis is false at the flag.
* `exists_pull_lineEulerOf` — the Euler class of a line bundle is pulled back
  from a projective space, which is what makes `Sq¹` kill each root.  It is true
  by unfolding: `lineEulerOf` is `eulerClass` of the classifying map, and
  `eulerClass` is that pullback.

## The wrap-around family

The split relation wants the lines as an `ℕ`-indexed family, while the flag has
`r` of them.  `flagLineFlat` reads the index modulo the rank, so every member is
a genuine line and its trace is one at *every* point, not only below the rank.
Cutting off with a zero bundle instead would reintroduce exactly the false
hypothesis the restricted relation was written to avoid, and there is in any case
no zero `Bundle`.  On the range the two families agree, which is all the relation
looks at.  `cc-lix-odd`'s `vLineFlatBundle` makes the same choice for `V`.

## Main declarations

* `flagLineFlat`, `sum_flagLineFlat` — the lines, indexed by a natural.
* `exists_pull_lineEulerOf` — a line's Euler class is pulled back from `ℂP^d`.
* `splitRelation_flag` — **the split relation at the flag.**
* `hasSplitting_flag` — **the splitting principle**, with nothing left open.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Wu

open CategoryTheory
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-! ## 1. Constant rank as a trace condition -/

/-- The rank hypothesis in the form `Bundle.flag_decomposition` takes it. -/
theorem trace_eq_of_rank (p : Bundle X ι) (r : ℕ) (hrank : ∀ x, p.rank x = r) (x : X) :
    (p x).trace = (r : ℂ) := by
  rw [Bundle.trace_eq_rank, hrank]

/-! ## 2. The lines of the flag, indexed by a natural -/

/-- The tautological lines of the top stage, indexed by a natural: the index is
read modulo the rank, so every member is a genuine line. -/
def flagLineFlat (p : Bundle X ι) (r l : ℕ) : Bundle (Bundle.Flag p r) ι :=
  Bundle.flagLine p r (l % r)

/-- Every member of the flat family is a line, at every index and every point. -/
theorem trace_flagLineFlat (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (l : ℕ)
    (w : Bundle.Flag p r) : (flagLineFlat p r l w).trace = 1 :=
  Bundle.trace_flagLine p (Nat.mod_lt l (by omega)) w

/-- On the range the flat family is the intended one. -/
theorem flagLineFlat_apply_of_lt (p : Bundle X ι) (r l : ℕ) (hl : l < r)
    (w : Bundle.Flag p r) : flagLineFlat p r l w = Bundle.flagLine p r l w := by
  show Bundle.flagLine p r (l % r) w = Bundle.flagLine p r l w
  rw [Nat.mod_eq_of_lt hl]

/-- **The decomposition of the pullback into the flat family.** -/
theorem sum_flagLineFlat (p : Bundle X ι) (r : ℕ) (hrank : ∀ x, p.rank x = r)
    (w : Bundle.Flag p r) :
    flagPullback p r w = ∑ l ∈ Finset.range r, flagLineFlat p r l w :=
  (Bundle.flag_decomposition p r (trace_eq_of_rank p r hrank) w).trans
    (Finset.sum_congr rfl fun l hl =>
      (flagLineFlat_apply_of_lt p r l (Finset.mem_range.mp hl) w).symm)

/-! ## 3. The roots -/

/-- **A line's Euler class is pulled back from a projective space.**  True by
unfolding: `lineEulerOf` is `eulerClass` of the classifying map of the
pushed-forward line, and `eulerClass` is the pullback of the generator. -/
theorem exists_pull_lineEulerOf [DecidableEq ι] (q : Bundle X ι)
    (hq : ∀ x, (q x).trace = 1) :
    ∃ (d : ℕ) (g : TopCat.of X ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      lineEulerOf q hq = pull g 2 h :=
  ⟨1 + tautCardOf ι,
    cmap (Bundle.classifyOne
      (Bundle.pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q)
      (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) q hq)),
    cpGen (1 + tautCardOf ι) (by omega), rfl⟩

/-- The roots of the split relation at the flag: the Euler classes of the
tautological lines. -/
def flagRoot [DecidableEq ι] (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (l : ℕ) :
    Hmod2 (TopCat.of (Bundle.Flag p r)) 2 :=
  lineEulerOf (flagLineFlat p r l) (trace_flagLineFlat p r hr1 l)

/-! ## 4. The split relation at the flag -/

/-- **The split relation at the flag.**  The decomposition of the pullback into
the tautological lines, fed to the restricted relation. -/
theorem splitRelation_flag [DecidableEq ι] (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, p.rank x = r)
    [CompactSpace (Bundle.Flag p r)] [Nonempty (Bundle.Flag p r)] :
    LerayHirschData.SplitRelation
      (lerayHirschData_of_graded (lerayHirschGraded_compact (flagPullback p r) r
        (rank_flagPullback p r hrank) hr1)) r (flagRoot p r hr1) :=
  splitRelation_of_sum_lt (flagPullback p r) r hr1 (rank_flagPullback p r hrank)
    (flagLineFlat p r) (fun l _ => trace_flagLineFlat p r hr1 l)
    (sum_flagLineFlat p r hrank) (flagRoot p r hr1) (fun _ _ => rfl)

/-! ## 5. The splitting principle -/

/-- **The splitting principle, with nothing left open.**  Over a compact
non-empty base a bundle of constant positive rank has a `Wu.SplittingData`: the
flag tower supplies the space, the injectivity, the roots and the relation, and
the compactness and non-emptiness of the tower are themselves consequences of
those of the base. -/
theorem hasSplitting_flag [DecidableEq ι] [CompactSpace X] [Nonempty X]
    (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, p.rank x = r) :
    Wu.HasSplitting (TopCat.of X)
      (lerayHirschData_of_graded (lerayHirschGraded_compact p r hrank hr1)).chern := by
  haveI : Nonempty (TopCat.of X) := ‹Nonempty X›
  haveI := flag_compactSpace p r
  haveI hflag : Nonempty (Bundle.Flag p r) := flag_nonempty p r hrank r le_rfl
  haveI : Nonempty (TopCat.of (Bundle.Flag p r)) := hflag
  exact hasSplitting_of_flagSplitRelation p r hr1 hrank (flagRoot p r hr1)
    (fun l => exists_pull_lineEulerOf (flagLineFlat p r l) (trace_flagLineFlat p r hr1 l))
    (splitRelation_flag p r hr1 hrank)

end

end Wu
end CharClass
end GroupApproximation
