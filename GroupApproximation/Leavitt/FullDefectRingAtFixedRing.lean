import GroupApproximation.Leavitt.OneSidedCompressorStabilized
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCountable
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring` at one ring: the ring calculation meets the criterion

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`.  This module is the
single seam between the two halves of its proof, and contains no mathematics of
its own beyond joining them.

* The ring calculation is `GroupApproximation.Leavitt.OneSidedCompressor*`: the
  core `L = EL₃(R)` inside `G = EL_n(R)`, the compressor `u`, the centralizer
  element `c`, the defect `d = [ucu⁻¹, ℓ]`, and — under the printed ideal
  condition on `e = 1 - st` — the saturation `𝔇_G(L) = ⊤`
  (`OneSidedCompressor.printedDefectOf_eq_top`).  Property `(T)` for the core
  comes from property `(T)` for `EL₃(R)` along the surjection
  `OneSidedCompressor.coreEmbeddingOfToCore`.
* The operator-algebraic conclusion is
  `Manuscript.OneSidedMFRadical.FullDefectRing.manuscriptSaturatedPrintedDefectRadical`:
  a countable group with property `(T)`, containing a property-`(T)` subgroup
  whose printed defect is everything, admits no nontrivial homomorphism to an
  MF group.

Joining them discharges `FullDefectAtFixedRing`, which every later statement of
`thm:full-defect-ring` and of `cor:simple-infinite-ring` and
`cor:one-sided-ring-maximal` carries as a leading hypothesis.

Countability of `G` is `FullDefectRing.countable_elementaryGroup`, transported
from the printed hypothesis "let `R` be a countable unital associative ring".
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators

/-- **`thm:full-defect-ring` at a fixed countable ring.**  Given `ts = 1` and
the printed ideal condition `R(1-st)R = R` in its indexed-sum form, and given
the two property-`(T)` inputs the printed proof takes from
Ershov--Jaikin-Zapirain, every homomorphism from `EL_n(R)` to an MF group is
trivial for every `n ≥ 4`.

The compressor, the centralizer element and the normal generation of `EL_n(R)`
by `d = [ucu⁻¹, ℓ]` are the landed rank-`n` calculation; this proof only
assembles their conclusions into the hypotheses of
`manuscriptSaturatedPrintedDefectRadical`. -/
theorem fullDefectAtFixedRing : FullDefectAtFixedRing := by
  intro R _ _ s t hts hfull n hn hT3 hTn M _ hM f x
  haveI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
  have hD : printedDefect (OneSidedCompressor.coreOf R hn) = ⊤ :=
    OneSidedCompressor.printedDefectOf_eq_top ⟨s, t, hts⟩ hn hfull
  have hL : HasKazhdanPropertyT.{0, 0} (OneSidedCompressor.coreOf R hn) :=
    OneSidedCompressor.coreOf_hasKazhdanPropertyT hn hT3
  exact (manuscriptSaturatedPrintedDefectRadical (elementaryGroup (Fin n) R)
    (OneSidedCompressor.coreOf R hn) hL hTn hD).2.2.1 M hM f x

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.FullDefectRing.fullDefectAtFixedRing
