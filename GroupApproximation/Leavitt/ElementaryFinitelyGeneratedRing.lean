import GroupApproximation.Leavitt.IntegralGeneration
import GroupApproximation.PropertyT.FinitelyGeneratedRing

/-!
# `EL_n(R)` is finitely generated over a finitely generated ring

`non_mf_groups_exist.tex`, proof of `thm:full-defect-ring`:

> The ring `𝒞` is finitely generated, so both groups have property~(T)
> by [EJZ], and `B` is finitely generated [BHV, Theorem 1.3.1].

`Leavitt.IntegralGeneration` proves this over any ring that is finitely
generated as a `ℤ`-algebra (`elementaryGroup_finitelyGenerated_int`), with
the generating set exhibited: the root matrices at the ring generators and at
`1`.  The printed hypothesis is `IsFinitelyGeneratedRing`, phrased with
`Subring.closure` rather than `Algebra.adjoin ℤ`, and
`PropertyT.FinitelyGeneratedRing` identifies the two
(`isFinitelyGeneratedRing_iff_finiteType_int`).  This module restates the
conclusion under the printed hypothesis, so the manuscript's `B` clause can be
cited in the manuscript's own vocabulary.
-/

namespace GroupApproximation

variable {R : Type*} [Ring R]

/-- **`EL_n(R)` is finitely generated whenever `R` is a finitely generated
ring and `n ≥ 3`.**  This is the printed `B` clause at a general coefficient
ring; the printed hypothesis is exactly `IsFinitelyGeneratedRing`, and the
proof is `elementaryGroup_finitelyGenerated_int` once that hypothesis is read
as `Algebra.FiniteType ℤ R`. -/
theorem elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing
    (hR : IsFinitelyGeneratedRing R) (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by
  haveI : Algebra.FiniteType ℤ R :=
    (isFinitelyGeneratedRing_iff_finiteType_int R).mp hR
  exact elementaryGroup_finitelyGenerated_int n hn

end GroupApproximation
