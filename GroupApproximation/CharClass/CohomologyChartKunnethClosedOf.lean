import GroupApproximation.CharClass.CohomologyChartInductionOf
import GroupApproximation.CharClass.CohomologyChartGenHypOf

/-!
# The projective-factor Künneth over a field, over the ring of `ℂP^d`

The coefficient-generic form of `CohomologyChartKunnethClosed`, with the one input that over `F₂`
was `ProjectiveSpaceRingClosed.cpGenHyp` named as a proposition: `CPRingOf K`, the nonvanishing of
the powers of every nonzero degree-two class of `ℂP^d` up to `d`.  It is supplied by the Gysin
sequence of the tautological circle bundle over `K` (`CPn.cupPowE_ne_zeroOf`), whose only
Leray–Hirsch input is the rank-two decomposition of `CohomologyChartRankTwoInterfaceOf`; so the
dependence is not circular.

## Main declarations

* `KnCP.CPRingOf` — the ring input over `K`.
* `KnCP.exists_ne_zero_two` — `H^2(ℂP^d; K)` has a nonzero element.
* `KnCP.cpSplitOf_closed`, `KnCP.flat_closedOf`, `KnCP.mvResVOf_surjective_closed`,
  `KnCP.cpTop_cup_injective_closedOf`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-- **The ring input over `K`.**  The powers of any nonzero degree-two class of `ℂP^d` are nonzero
up to `d`. -/
def CPRingOf (K : Type) [Field K] : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (h : Hmod K (CPtop d) 2), h ≠ 0 → ∀ m : ℕ, m ≤ d → cupPowE h m ≠ 0

variable (K : Type) [Field K]

/-- Generation on `ℂP^e`, from the ring input. -/
theorem cpGenHypOf_of_ring (hring : CPRingOf K) (e : ℕ) (he : 1 ≤ e) : CPGenHypOf K e :=
  cpGenHypOf_of_cupPowE_ne_zeroOf K e (fun h h0 m hm => hring e he h h0 m hm)

/-- `H^2(ℂP^d; K)` is a line for `d ≥ 1`, so it has a nonzero element. -/
theorem exists_ne_zero_two (d : ℕ) (hd : 1 ≤ d) : ∃ h : Hmod K (CPtop d) 2, h ≠ 0 := by
  obtain ⟨L⟩ := (hasCPCohomologyOf_CP K d).1 1 hd
  exact ⟨lineGen L, lineGen_ne_zero L⟩

/-- **The product form over `K`, at every rank, over the ring input.** -/
theorem cpSplitOf_closed (hring : CPRingOf K) (d : ℕ) (hd : 1 ≤ d) : CPSplitOf K d :=
  cpSplitOf_of_cpGenHypOf K (fun e he => cpGenHypOf_of_ring K hring e (by omega)) d hd

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **Flatness over `K`, over the ring input.** -/
theorem flat_closedOf (hring : CPRingOf K) (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0)
    (k m : ℕ) (hk : 2 + m = k) (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) :
    ∃ e : Hmod K (TopCat.of U) k,
      (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom w
        = pull (cpPrSub U d (interUSet U d)) k e :=
  flat_of_cpSplitOf K U d h h0 (cpSplitOf_closed K hring d hd) k m hk w

/-- **Surjectivity of the restriction over `K`, in every degree, over the ring input.** -/
theorem mvResVOf_surjective_closed (hring : CPRingOf K) (hd : 1 ≤ d) (k : ℕ)
    (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod K (cpProdTop U d) k,
      (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  obtain ⟨h, h0⟩ := exists_ne_zero_two K d hd
  exact mvResVOf_surjective_of_cpSplit_allOf K U d hd h h0 (cpSplitOf_closed K hring d hd) k w

/-- **Uniqueness of the `cpTopOf`-coefficient over `K`, over the ring input.** -/
theorem cpTop_cup_injective_closedOf (hring : CPRingOf K) (hd : 1 ≤ d) (m : ℕ)
    (b : Hmod K (TopCat.of U) m) (hcup : cup (cpTopOf K U d) (pull (cpPrU U d) m b) = 0) :
    b = 0 := by
  obtain ⟨h, h0⟩ := exists_ne_zero_two K d hd
  exact cpTop_cup_injectiveOf K U d hd h h0 (cpSplitOf_closed K hring d hd) m b hcup

end KnCP

end

end GroupApproximation.CharClass
