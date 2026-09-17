import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergPerfect.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HopfFiveTerm.Step
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedKill.General
import GroupApproximation.Meta.AxiomGuard

/-!
# The padded kill: `H₂(E₃ R) = 0` kills `stab(K₂(3, R))` inside `St₄(R)`

Lane `sk-rows-16` (carto-sk-rows, section 4).  Ring-generic infrastructure on Khanh's route
(arXiv:2609.08428v1, Theorem 5.4) to the rank-four `K₂` gap behind tex 733.  No single tex sentence
is formalized here, and nothing here is a hypothesis of any `manuscriptSentence_*`.

## Statement

For every ring `R` whose rank-three elementary group `E₃(R)` has trivial Hopf multiplier
(`HopfFiveTerm.HopfMultiplierTrivial`, presentation-free form),
`stab(K₂(3, R)) = 1` in `St₄(R)`, i.e. `K₂(3, R) ≤ ker (St₃(R) → St₄(R))`.

## Truth check

* `St₃(R)` is perfect (`SteinbergPerfect.steinberg_fin_three_commutator_eq_top`, proved).
* Five-term step (`HopfFiveTerm.le_commutator_of_hopfMultiplierTrivial`, proved):
  `St₃(R) ↠ E₃(R)` with perfect source and `H₂(E₃ R) = 0` gives `K₂(3) ≤ ⁅St₃, K₂(3)⁆`.
* Khanh's padded centrality (lane `sk-rows-14`): `stab(K₂(m, R)) ≤ Z(St_{m+1}(R))` for `m ≥ 2`
  and every ring.  The notes of carto-sk-rows record it as TRUE via the column/row action argument
  (for `y ∈ K₂(m)`, `stab y` fixes all last-column and last-row root elements, and these generate
  `St_{m+1}` through `x_ij(a) = ⁅x_{i,m+1}(a), x_{m+1,j}(1)⁆`).  Only the padded form is used; the
  unpadded `K₂(n) ≤ Z(Stₙ)` is NOT claimed.
* Then `stab K₂(3) ≤ stab ⁅St₃, K₂(3)⁆ = ⁅stab St₃, stab K₂(3)⁆ ≤ ⁅St₄, Z(St₄)⁆ = 1`
  (`PaddedKill.map_eq_bot_of_le_commutator_of_map_le_center`).

So the lane target `stab_K2_three_eq_bot_of_hopf` is TRUE.

## Remaining interface

Lane `sk-rows-14` has not landed (grep: no `stab_K2_le_center` / `PaddedCentralityStatement` in
the repo).  It is stated below as `PaddedCentralityStatement` (the lane-14 theorem verbatim,
quantified over `m ≥ 2` and rings in universe `v`), and the lane target is proved as
`stab_K2_three_eq_bot_of_hopf_of_paddedCentrality`.  The sharper
`stab_K2_three_eq_bot_of_hopf_of_center` assumes only the `m = 3` instance for the one ring `R`,
which is strictly weaker than `PaddedCentralityStatement`.  Once lane 14 lands, the unconditional
form is `stab_K2_three_eq_bot_of_hopf_of_center R h (stab_K2_le_center 3 (by norm_num) R)`.

The input `HopfMultiplierTrivial (E₃ L)` for the binary Leavitt algebra `L` is Khanh's acyclicity
theorem (research input; a documented gap, not a hypothesis of any manuscript sentence).
-/

universe v

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill

open GroupApproximation.BooneHigman.SteinbergBasic (St K2n stab)
open GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm (HopfMultiplierTrivial
  le_commutator_of_hopfMultiplierTrivial)

/-- Interface of lane `sk-rows-14` (Khanh's padded centrality), not yet on disk: for every
`m ≥ 2` and every ring `R` in universe `v`, the stabilized `K₂(m, R)` is central in
`St_{m+1}(R)`. -/
def PaddedCentralityStatement.{w} : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (R : Type w) [Ring R],
    (K2n m R).map (stab m R) ≤ Subgroup.center (St (m + 1) R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.PaddedCentralityStatement

/-- **Five-term step in rank three.**  If `E₃(R)` has trivial Hopf multiplier, then
`K₂(3, R) ≤ ⁅St₃(R), K₂(3, R)⁆`.  Unconditional apart from the printed hypothesis. -/
theorem K2_three_le_commutator_of_hopf (R : Type v) [Ring R]
    (h : HopfMultiplierTrivial (elementaryGroup (Fin 3) R)) :
    K2n 3 R ≤ ⁅(⊤ : Subgroup (St 3 R)), K2n 3 R⁆ :=
  le_commutator_of_hopfMultiplierTrivial (SteinbergGroup.projection (I := Fin 3) (R := R))
    SteinbergGroup.projection_surjective
    (SteinbergPerfect.steinberg_fin_three_commutator_eq_top R) h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.K2_three_le_commutator_of_hopf

/-- **Padded kill, local form.**  If `E₃(R)` has trivial Hopf multiplier and `stab(K₂(3, R))` is
central in `St₄(R)`, then `stab(K₂(3, R)) = ⊥`. -/
theorem stab_K2_three_eq_bot_of_hopf_of_center (R : Type v) [Ring R]
    (h : HopfMultiplierTrivial (elementaryGroup (Fin 3) R))
    (hC : (K2n 3 R).map (stab 3 R) ≤ Subgroup.center (St (3 + 1) R)) :
    (K2n 3 R).map (stab 3 R) = ⊥ :=
  map_eq_bot_of_le_commutator_of_map_le_center (stab 3 R) (K2_three_le_commutator_of_hopf R h) hC

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.stab_K2_three_eq_bot_of_hopf_of_center

/-- **Padded kill** (lane `sk-rows-16` target), reduced to lane 14's padded centrality:
`H₂(E₃ R) = 0` gives `stab(K₂(3, R)) = ⊥` in `St₄(R)`. -/
theorem stab_K2_three_eq_bot_of_hopf_of_paddedCentrality
    (hPC : PaddedCentralityStatement.{v}) (R : Type v) [Ring R]
    (h : HopfMultiplierTrivial (elementaryGroup (Fin 3) R)) :
    (K2n 3 R).map (stab 3 R) = ⊥ :=
  stab_K2_three_eq_bot_of_hopf_of_center R h (hPC 3 (by norm_num) R)

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.stab_K2_three_eq_bot_of_hopf_of_paddedCentrality

/-- Kernel form of the padded kill: `K₂(3, R) ≤ ker (stab : St₃(R) → St₄(R))`. -/
theorem K2_three_le_ker_stab_of_hopf_of_paddedCentrality
    (hPC : PaddedCentralityStatement.{v}) (R : Type v) [Ring R]
    (h : HopfMultiplierTrivial (elementaryGroup (Fin 3) R)) :
    K2n 3 R ≤ (stab 3 R).ker :=
  (Subgroup.map_eq_bot_iff (K2n 3 R)).mp
    (stab_K2_three_eq_bot_of_hopf_of_paddedCentrality hPC R h)

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill.K2_three_le_ker_stab_of_hopf_of_paddedCentrality

end GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedKill
