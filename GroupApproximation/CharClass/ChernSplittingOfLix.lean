import GroupApproximation.CharClass.ChernSplittingOfOpsAdapter
import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.LIXBaseInstances
import GroupApproximation.Analysis.LIXProjectiveSpaceModel

/-!
# The splitting principle over `F_p` at the mapping torus of the tower

Lane `lx-splitK`, prefix `CharClass/ChernSplittingOf*`.

`ChernSplittingOf.hasSplittingPN_of_compactOps` at the real bundle of Step D: the mapping torus
`W_g = KGen.lixBundle n G hGc hGu` over `S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`, of constant rank
`lixRank n dd`.  The base is compact and non-empty, as a product of spheres and projective spaces.
So the inputs are the named compact Leray–Hirsch theorem over `F_p`, the reduced powers, and the
operation on the base.  That operation is a free argument, intertwined with the reduced powers at
the Chern classes, so that the torus data (`Gen.RealTorusModP`) can supply its own.

The Chern classes in the conclusion are exactly
`(LerayHirschDataEvenOf.of_graded (hLH _ (lixBundle n G hGc hGu) (lixRank n dd) _ _)).chern`, the
carrier `lx-bundleP` feeds to the slice value and the degree bookkeeping.

## Main declarations

* `KGen.hasSplittingPN_lixBundleOf` — for any operation `PN` on the base intertwined at the Chern
  classes.
* `KGen.hasSplittingPN_lixBundleOf_self` — with `PN := ops.P` of the base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace KGen

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.ChernSplittingOf

noncomputable section

/-- **The splitting principle over `F_p` at the mapping torus**, for every corner unitary field `G`,
from compact Leray–Hirsch over `F_p`, the reduced powers, and an operation `PN` on the base
intertwined with them at the Chern classes. -/
theorem hasSplittingPN_lixBundleOf (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod (ZMod p) (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2)
    (hLH : CompactLerayHirschDualOf (ZMod p) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) hgen)
    (ops : OddPTotal.EvenReducedPowers p)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (PN : ℕ → Gen.evenPart (ZMod p) (lixN n dd) →+ Gen.evenPart (ZMod p) (lixN n dd))
    (hnat : ∀ i : ℕ,
      ops.P (TopCat.of (Bundle.Flag (lixBundle n G hGc hGu) (lixRank n dd))) i
          (Gen.evenMap (ZMod p) (cmap (Bundle.flagProj (lixBundle n G hGc hGu) (lixRank n dd)))
            ((LerayHirschDataEvenOf.of_graded
              (hLH (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
                (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern (i + 1)))
        = Gen.evenMap (ZMod p) (cmap (Bundle.flagProj (lixBundle n G hGc hGu) (lixRank n dd)))
            (PN i ((LerayHirschDataEvenOf.of_graded
              (hLH (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
                (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern (i + 1)))) :
    ParityP.HasSplittingPN p
      (LerayHirschDataEvenOf.of_graded
        (hLH (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
          (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern PN 1 :=
  hasSplittingPN_of_compactOps p hgen hLH ops (lixBundle n G hGc hGu) (lixRank n dd)
    (one_le_lixRank n dd) (rank_lixBundle n G hGc hGu) PN hnat

/-- **The splitting principle over `F_p` at the mapping torus, with the reduced powers of the
base.** -/
theorem hasSplittingPN_lixBundleOf_self (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod (ZMod p) (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2)
    (hLH : CompactLerayHirschDualOf (ZMod p) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) hgen)
    (ops : OddPTotal.EvenReducedPowers p)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ParityP.HasSplittingPN p
      (LerayHirschDataEvenOf.of_graded
        (hLH (↥sphereOne × Gen.baseM n dd) (lixBundle n G hGc hGu) (lixRank n dd)
          (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd))).chern
      (ops.P (lixN n dd)) 1 :=
  hasSplittingPN_of_compactOps_self p hgen hLH ops (lixBundle n G hGc hGu) (lixRank n dd)
    (one_le_lixRank n dd) (rank_lixBundle n G hGc hGu)

end

#audit_axioms hasSplittingPN_lixBundleOf
#audit_axioms hasSplittingPN_lixBundleOf_self

end KGen
end CharClass
end GroupApproximation
