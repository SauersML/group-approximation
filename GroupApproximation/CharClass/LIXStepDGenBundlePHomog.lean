import GroupApproximation.CharClass.LIXStepDGenBundlePReal
import GroupApproximation.CharClass.ChernClassesEvenHomogOf
import GroupApproximation.CharClass.ChernSplittingOfLHBridge
import GroupApproximation.CharClass.LIXStepDGenTorusPLix
import GroupApproximation.Meta.AxiomGuard

/-!
# The bundle data of Step D mod `p` at every stage, from the reduced powers alone

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

`Gen.nonempty_realBundleModP_lixChernDegOf_stages` (`CharClass/LIXStepDGenBundlePReal.lean`) is the
first clause of `NinetyNineProblems.LemmaTwoPowersModPData` over its binders: the torus data, the
compact Leray–Hirsch data `LE` and `LV`, the homogeneity `hhomE` of the Chern classes of `LE`, a unit
vector, the normalisation, and the narrowed splitting principle.  This file discharges them in turn.

* `hhomE` is lane `lx-lhK-b`'s `LerayHirschDataEvenOf.chern_eq_of_graded`, read at the type of the
  binder (`Gen.lixBundle_chern_homogOf`).
* `LE` and `LV` are lane `lx-splitK`'s compact Leray–Hirsch over `F_p` at the generator
  `ChernSplittingOf.cpGenOf`, `ChernSplittingOf.compactLerayHirschDualOf_cpGen`, applied to the
  mapping-torus bundle over `S¹ × S^{2n+1} × ∏ᵢ ℂP^{dᵢ}` and to `V` pushed into the doubled index over
  `∏ᵢ ℂP^{dᵢ}`; the ranks are `KGen.rank_lixBundle` and `Gen.rank_vBundleY`.
* The torus data are lane `lx-torusP`'s `Gen.realTorusModP_lixStage ops n`, whose powers are
  `ops.P` at the base.
* The splitting principle is lane `lx-splitK`'s `KGen.hasSplittingPN_lixBundleOf_self`, with
  normalisation `1`, at the same compact Leray–Hirsch term, so every piece meets by `rfl`.

What remains is one argument, the reduced powers `ops : OddPTotal.EvenReducedPowers p` (lane
`lx-pzero`).  The classes of the output are
`k ↦ of (2k) (KGen.lixChernDegOf (ZMod p) n (lixDD n j) (cpGenOf …) W k)`.

## Main results

* `Gen.lixBundle_chern_homogOf` — **the producer of `hhomE`**, in the binder's shape.
* `Gen.nonempty_realBundleModP_lixChernDegOf_stages_homog` — the stage family with `hhomE`
  discharged.
* `Gen.nonempty_realBundleModP_lixOps_stages` — **the stage family from the reduced powers alone**.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open ParityP

namespace Gen

variable {ℓ : ℕ}

/-- **The producer of `hhomE`**: the Leray–Hirsch Chern classes of the mapping-torus bundle are
homogeneous, `chern k` in degree `2k`, read at the carrier `KGen.lixN n dd` with `.1`. -/
theorem lixBundle_chern_homogOf (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2)
    {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ} (hGc : Continuous G)
    (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x))
    (LE : LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd)) :
    ∀ k : ℕ, ∃ x : TotalPieceOf K (KGen.lixN n dd) (2 * k),
      ((LerayHirschDataEvenOf.of_graded LE).chern k).1
        = TotalHOf.of K (KGen.lixN n dd) (2 * k) x := by
  intro k
  obtain ⟨x, hx⟩ := LerayHirschDataEvenOf.chern_eq_of_graded LE k
  exact ⟨x, hx⟩

/-- **The stage family with `hhomE` discharged**: the first clause of
`NinetyNineProblems.LemmaTwoPowersModPData` over the torus data, the compact Leray–Hirsch data, a
unit vector, the normalisation and the narrowed splitting principle. -/
theorem nonempty_realBundleModP_lixChernDegOf_stages_homog (n p : ℕ) [Fact p.Prime]
    (T : ∀ j, RealTorusModP n (ZMod p) (KnLix.prY n (LIX.Gen.lixDD n j))
      (KnLix.prS1 n (LIX.Gen.lixDD n j)) (KnLix.prSodd n (LIX.Gen.lixDD n j))
      (sphereTopClassOf (ZMod p) 1 (by omega)) (sphereTopClassOf (ZMod p) (2 * n + 1) (by omega)))
    (hgen : ∀ j : ℕ, Hmod (ZMod p)
      (CPtop (1 + tautCardOf (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)))) 2)
    (LE : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ) (hGc : Continuous G)
      (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x)),
      LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
        (LH.tautEulerDualK (ZMod p) (hgen j) (KGen.lixBundle n G hGc hGu))
        (KGen.lixRank n (LIX.Gen.lixDD n j)))
    (LV : ∀ j : ℕ, LerayHirschGraded
      (projMapOf (pushforward
        (Sum.inr : VIdx n (LIX.Gen.lixDD n j) → VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
        Sum.inr_injective (vBundleY n (LIX.Gen.lixDD n j))))
      (LH.tautEulerDualK (ZMod p) (hgen j)
        (pushforward
          (Sum.inr : VIdx n (LIX.Gen.lixDD n j) → VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          Sum.inr_injective (vBundleY n (LIX.Gen.lixDD n j))))
      (KGen.lixRank n (LIX.Gen.lixDD n j)))
    (q : ↥(unitVectors (Fin (n + 1))))
    (κ : ℤ) (hκ : IsUnit (κ : ZMod p))
    (hwu : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ) (hGc : Continuous G)
      (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x)),
      HasSplittingPN p (LerayHirschDataEvenOf.of_graded (LE j G hGc hGu)).chern (T j).PN κ) :
    ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
      Nonempty (RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (fun k => TotalHOf.of (ZMod p) (KGen.lixN n (LIX.Gen.lixDD n j)) (2 * k)
          (KGen.lixChernDegOf (ZMod p) n (LIX.Gen.lixDD n j) (hgen j)
            (mappingTorus (Vmat n) G circHoriz circHeight) k))) :=
  nonempty_realBundleModP_lixChernDegOf_stages n p T hgen LE
    (fun j _ hGc hGu => lixBundle_chern_homogOf (ZMod p) n (LIX.Gen.lixDD n j) (hgen j) hGc hGu
      (LE j _ hGc hGu))
    LV q κ hκ hwu

/-- **The stage family from the reduced powers alone.**  At every stage `j` and every corner unitary
`G`, the bundle data of Step D mod `p` exist over lane `lx-torusP`'s torus data
`Gen.realTorusModP_lixStage ops n j`, with the classes of `lx-stepcK-local`'s degreewise Chern
classes at the generator `ChernSplittingOf.cpGenOf`.  The only argument is the reduced powers. -/
theorem nonempty_realBundleModP_lixOps_stages (n p : ℕ) [Fact p.Prime]
    (ops : OddPTotal.EvenReducedPowers p) :
    ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
      Nonempty (RealBundleModP p (LIX.Gen.lixDD n j) (realTorusModP_lixStage ops n j)
        (fun k => TotalHOf.of (ZMod p) (KGen.lixN n (LIX.Gen.lixDD n j)) (2 * k)
          (KGen.lixChernDegOf (ZMod p) n (LIX.Gen.lixDD n j)
            (ChernSplittingOf.cpGenOf (ZMod p)
              (1 + tautCardOf (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))) (by omega))
            (mappingTorus (Vmat n) G circHoriz circHeight) k))) :=
  nonempty_realBundleModP_lixChernDegOf_stages_homog n p (realTorusModP_lixStage ops n)
    (fun j => ChernSplittingOf.cpGenOf (ZMod p)
      (1 + tautCardOf (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))) (by omega))
    (fun j G hGc hGu => ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p)
      (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
      (↥sphereOne × baseM n (LIX.Gen.lixDD n j)) (KGen.lixBundle n G hGc hGu)
      (KGen.lixRank n (LIX.Gen.lixDD n j)) (KGen.rank_lixBundle n G hGc hGu)
      (KGen.one_le_lixRank n (LIX.Gen.lixDD n j)))
    (fun j => ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p)
      (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
      (baseY (LIX.Gen.lixDD n j))
      (pushforward
        (Sum.inr : VIdx n (LIX.Gen.lixDD n j) → VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
        Sum.inr_injective (vBundleY n (LIX.Gen.lixDD n j)))
      (KGen.lixRank n (LIX.Gen.lixDD n j))
      (fun y => (LH.rank_pushforward
          (Sum.inr : VIdx n (LIX.Gen.lixDD n j) → VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          Sum.inr_injective (vBundleY n (LIX.Gen.lixDD n j)) y).trans
        (rank_vBundleY n (LIX.Gen.lixDD n j) y))
      (KGen.one_le_lixRank n (LIX.Gen.lixDD n j)))
    (Classical.arbitrary _) 1 (by simp)
    (fun j G hGc hGu => KGen.hasSplittingPN_lixBundleOf_self p n (LIX.Gen.lixDD n j) _
      (ChernSplittingOf.compactLerayHirschDualOf_cpGen (ZMod p) _) ops G hGc hGu)

end Gen

#audit_axioms Gen.lixBundle_chern_homogOf
#audit_axioms Gen.nonempty_realBundleModP_lixChernDegOf_stages_homog
#audit_axioms Gen.nonempty_realBundleModP_lixOps_stages

end CharClass
end GroupApproximation

end
