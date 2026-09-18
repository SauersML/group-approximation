import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneReduce
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGen
import GroupApproximation.Meta.AxiomGuard

/-!
# `czK2FngTorus_GtOneStatement` reduced from rank four to rank three (lane bh-met-93o, endpoint)

Target: `czK2FngTorus_GtOneStatement`, the `m > 1` half of `CZK2FngRankFourStatement`.
**Not closed outright.**

**Proved outright.**  `czK2FngGtOne_k2_le_map` gives surjective stability
`K₂(4, ℤ[1/m]) ≤ stab K₂(3, ℤ[1/m])` for **every** `m > 0`.  It needs no hypothesis and no
literature input.  The proof runs the rank-three length reduction at every `m`, and the word
statement comes from the support lemma `czStabGen_mem_map_of_off`.  (Before this lane the
statement was known only for `m = 1`.)  With `czK2Fng_succ_of_le_map`, it gives
`czK2FngGtOne_succ`: `K₂(3, ℤ[1/m])` finitely normally generated implies the same for
`K₂(4, ℤ[1/m])`.

**Remaining gap.**  `czK2FngGtOne_RankThreeStatement`: for all `m > 1`, `K₂(3, ℤ[1/m])` is
finitely normally generated in `St_3(ℤ[1/m])`.  It gives
* the target `czK2FngTorus_GtOneStatement` (`czK2FngGtOne_gtOne_of_rankThree`), and
* the full `CZK2FngRankFourStatement` (`czK2FngGtOne_rankFour_of_rankThree`).

For the second, the case `m = 1` is `czK2FngTorus_k2ThreeOne_fng`.

**Truth check.**  `St_3(ℤ[1/m])` is finitely generated (`czK2Fng_steinbergAway_fg m 3`).
`E_3(ℤ[1/m]) = SL_3(ℤ[1/m])` is finitely presented: it is an S-arithmetic group of a split
simple group of rank `2` (Behr; Borel–Serre).  So the kernel is finitely normally generated
(`czK2Fng_k2_of_fg_of_fp`).  This is a truth check only.  It is not used as a hypothesis.

**Strength (LOUD).**  `czK2FngGtOne_RankThreeStatement` is **not logically weaker** than the
target.
* It implies the target (proved here).
* The converse is not formal.  It would need `K₂(3) → K₂(4)` to be injective (injective
  stability) together with the normal closures to match.
* It is not an equivalent restatement either.  It says nothing about rank four, and its generating
  set is a subgroup one rank lower, not a new set for the same group.

It is **strictly smaller in proof content**.
* The whole rank-four part, i.e. the step `K₂(4) ≤ stab K₂(3)`, is discharged here outright.
* What remains is the rank-three group `St_3(ℤ[1/m])`.  Its relevant presentation input is
  `SL_3` (rank `2`) rather than `SL_4` (rank `3`).
* The same rank-three statement at `m = 1` is already proved in the repository.

**Avoided.**  No symbols route, no `czRankFourFP_*`, no Behr hypothesis, no homotopy invariance,
no `SL = E` at rank `k+1` beyond `SL_2(ℤ[1/m]) = E_2` (Euclidean), no Step A, no K₂ excision.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **The one-step stability, outright.**  For `m > 0`, finite normal generation of
`K₂(3, ℤ[1/m])` implies finite normal generation of `K₂(4, ℤ[1/m])`. -/
theorem czK2FngGtOne_succ {m : ℕ} (hm : 0 < m)
    (hfn : (K2 (Fin 3) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated) :
    (K2 (Fin 4) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated :=
  czK2Fng_succ_of_le_map (n := 3) hfn (czK2FngGtOne_k2_le_map hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_succ

/-- **The isolated gap (lane bh-met-93o).**  For all `m > 1`, `K₂(3, ℤ[1/m])` is finitely
normally generated in `St_3(ℤ[1/m])`.  It is true (`SL_3(ℤ[1/m])` is finitely presented), and it
is one rank below the target.  It is **not** logically weaker than the target (see the module
docstring). -/
def czK2FngGtOne_RankThreeStatement : Prop :=
  ∀ m : ℕ, 1 < m → (K2 (Fin 3) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_RankThreeStatement

/-- **The reduction to `CZK2FngRankFourStatement`.**  The case `m = 1` is already proved. -/
theorem czK2FngGtOne_rankFour_of_rankThree (h : czK2FngGtOne_RankThreeStatement) :
    CZK2FngRankFourStatement := by
  intro m hm
  refine czK2FngGtOne_succ hm ?_
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · exact h m h1
  · obtain rfl : m = 1 := by omega
    exact czK2FngTorus_k2ThreeOne_fng

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_rankFour_of_rankThree

/-- **The target from the rank-three gap.** -/
theorem czK2FngGtOne_gtOne_of_rankThree (h : czK2FngGtOne_RankThreeStatement) :
    czK2FngTorus_GtOneStatement :=
  czK2FngTorus_gtOne_of_rankFour (czK2FngGtOne_rankFour_of_rankThree h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_gtOne_of_rankThree

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
