import GroupApproximation.CharClass.ChernSplittingOfLix
import GroupApproximation.CharClass.LerayHirschCompactClosedOf
import GroupApproximation.CharClass.ProjectiveSpaceComputationOf

/-!
# The named Leray–Hirsch input, discharged, and the splitting principle at the mapping torus

Lane `lx-splitK`, prefix `CharClass/ChernSplittingOf*`.

`ChernSplittingOf.CompactLerayHirschDualOf K ι hgen` is the one geometric input of the splitting
principle over `K`.  Lane `lx-lhK-b` proves compact Leray–Hirsch over a field for every nonzero
class `hgen` (`LH.lerayHirschGraded_compactDualOf`), and `H²(ℂP^N; K)` is a line for `N ≥ 1`
(`hasCPCohomologyOf_CP`), so a nonzero class exists.  This file puts the two together.

## Main declarations

* `ChernSplittingOf.compactLerayHirschDualOf_of_ne_zero` — the named input, for every nonzero `hgen`.
* `ChernSplittingOf.cpGenOf`, `cpGenOf_ne_zero` — a nonzero class of `H²(ℂP^N; K)`, `N ≥ 1`.
* `ChernSplittingOf.compactLerayHirschDualOf_cpGen` — the named input at that class.
* `KGen.hasSplittingPN_lixBundle` — **the splitting principle over `F_p` at the mapping torus**, with
  compact Leray–Hirsch discharged; the inputs are the reduced powers and an operation on the base
  intertwined with them at the Chern classes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

namespace ChernSplittingOf

/-- **The named compact Leray–Hirsch input, for every nonzero class.** -/
theorem compactLerayHirschDualOf_of_ne_zero (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0) :
    CompactLerayHirschDualOf K ι hgen := by
  intro Z _ _ _ q s hs hs1
  exact LH.lerayHirschGraded_compactDualOf K q s hs hs1 hgen hgen0

/-- **A nonzero degree-two class of `ℂP^N` over a field**, `N ≥ 1`: the preimage of `1` under a
linear equivalence `H²(ℂP^N; K) ≃ K`. -/
def cpGenOf (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N) : Hmod K (CPtop N) 2 :=
  ((hasCPCohomologyOf_CP K N).1 1 hN).some.symm (1 : K)

theorem cpGenOf_ne_zero (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N) : cpGenOf K N hN ≠ 0 := by
  intro h
  have h1 : ((hasCPCohomologyOf_CP K N).1 1 hN).some (cpGenOf K N hN) = 1 :=
    LinearEquiv.apply_symm_apply _ _
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **The named compact Leray–Hirsch input at the class `cpGenOf`.** -/
theorem compactLerayHirschDualOf_cpGen (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] :
    CompactLerayHirschDualOf K ι (cpGenOf K (1 + tautCardOf ι) (by omega)) :=
  compactLerayHirschDualOf_of_ne_zero K ι _ (cpGenOf_ne_zero K _ _)

end ChernSplittingOf

namespace KGen

open GroupApproximation.CharClass.ChernSplittingOf

/-- **The splitting principle over `F_p` at the mapping torus, with compact Leray–Hirsch
discharged.**  For every corner unitary field `G`, the Chern classes over `F_p` of `W_g` split, from
the reduced powers and an operation `PN` on the base intertwined with them at the Chern classes. -/
theorem hasSplittingPN_lixBundle (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ)
    (ops : OddPTotal.EvenReducedPowers p)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (PN : ℕ → Gen.evenPart (ZMod p) (lixN n dd) →+ Gen.evenPart (ZMod p) (lixN n dd))
    (hnat : ∀ i : ℕ,
      ops.P (TopCat.of (Bundle.Flag (lixBundle n G hGc hGu) (lixRank n dd))) i
          (Gen.evenMap (ZMod p) (cmap (Bundle.flagProj (lixBundle n G hGc hGu) (lixRank n dd)))
            ((LerayHirschDataEvenOf.of_graded
              (compactLerayHirschDualOf_cpGen (ZMod p) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)
                (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
                (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern (i + 1)))
        = Gen.evenMap (ZMod p) (cmap (Bundle.flagProj (lixBundle n G hGc hGu) (lixRank n dd)))
            (PN i ((LerayHirschDataEvenOf.of_graded
              (compactLerayHirschDualOf_cpGen (ZMod p) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)
                (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
                (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern (i + 1)))) :
    ParityP.HasSplittingPN p
      (LerayHirschDataEvenOf.of_graded
        (compactLerayHirschDualOf_cpGen (ZMod p) (Gen.VIdx n dd ⊕ Gen.VIdx n dd)
          (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
          (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern PN 1 :=
  hasSplittingPN_lixBundleOf p n dd _ (compactLerayHirschDualOf_cpGen (ZMod p) _) ops G hGc hGu
    PN hnat

end KGen

end

#audit_axioms ChernSplittingOf.compactLerayHirschDualOf_of_ne_zero
#audit_axioms ChernSplittingOf.cpGenOf
#audit_axioms ChernSplittingOf.cpGenOf_ne_zero
#audit_axioms ChernSplittingOf.compactLerayHirschDualOf_cpGen
#audit_axioms KGen.hasSplittingPN_lixBundle

end CharClass
end GroupApproximation
