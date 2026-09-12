import GroupApproximation.CharClass.LIXStepDGenBundlePLix
import GroupApproximation.CharClass.CohomologyKunnethLixNOf
import GroupApproximation.CharClass.SliceTorusOf
import GroupApproximation.CharClass.LIXKGenChernOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The bundle data of Step D mod `p` at the real mapping torus, from the compact Leray–Hirsch data

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

`Gen.realBundleModP_of_split` (`CharClass/LIXStepDGenBundleP.lean`) builds the bundle data of
Step D mod `p` from three named inputs.  At the geometric base `N = S¹ × S^{2n+1} × ∏ᵢ ℂP^{dᵢ}` of
the tower, over a field `K`, this file discharges every input that is a theorem of a peer lane:

* the Künneth split, `KnLix.evenKunnethSplitOf` (lane `lx-kunneth`);
* the slice section `KnLix.slice n dd southPole q` with its two identities
  `KnLix.slice_map_prY_map` and `KnLix.slice_map_zClass` (lane `lx-kunneth`);
* the slice value `Gen.sliceValue_lixBundleOf` (lane `lx-sliceK`), at the south pole where the
  mapping torus is `V`;
* the link to the degreewise classes, `KGen.lixChernDegOf_mappingTorus` (lane `lx-stepcK-local`).

What stays an argument is exactly what those lanes take as input: the torus data `T` on the
geometric projections, the two compact Leray–Hirsch data `LE` (the mapping-torus bundle) and `LV`
(its restriction to the slice, pushed into the doubled index), the homogeneity of the Chern classes
of `LE` (`hhomE`, which is `LerayHirschDataEvenOf.chern_eq_of_graded LE` of lane `lx-lhK-b`), a unit
vector `q`, the normalisation with its unit property and `p = 0` on the base, and the narrowed
splitting principle for the Chern classes of `LE`.

The classes of the output are `k ↦ of (2k) (KGen.lixChernDegOf K n dd hgen W k)`, the `γfun` of
`NinetyNineProblems.LemmaTwoPowersModPData`, so its link to the top class is `rfl` at the consumer.

The Chern classes of `LE` live in the even part of `TopCat.of (↥sphereOne × baseM n dd)`, which is
`KGen.lixN n dd` only after unfolding a `def`; a type ascription to `TotalHOf K (KGen.lixN n dd)`
does not find the coercion through it, so the classes are read with `.1` and every equation is
stated at the type of its left-hand side.

## Main results

* `Gen.coe_chern_eq_lixChernDegOf` — the Leray–Hirsch Chern classes are the degreewise classes.
* `Gen.realBundleModP_lixChernDegOf` — **the bundle data at the real mapping torus**.
* `Gen.nonempty_realBundleModP_lixChernDegOf_stages` — the existence form at every stage over `F_p`,
  the first clause of `NinetyNineProblems.LemmaTwoPowersModPData`.
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

/-- **The Leray–Hirsch Chern classes of the mapping torus are the degreewise classes**: at every
index `k`, the even class `chern k` of `LE` is `of (2k)` of `KGen.lixChernDegOf K n dd hgen W k`,
given that the classes are homogeneous. -/
theorem coe_chern_eq_lixChernDegOf (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2)
    {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ} (hGc : Continuous G)
    (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x))
    (LE : LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd))
    (hhomE : ∀ k : ℕ, ∃ x : TotalPieceOf K (KGen.lixN n dd) (2 * k),
      ((LerayHirschDataEvenOf.of_graded LE).chern k).1
        = TotalHOf.of K (KGen.lixN n dd) (2 * k) x) :
    (fun k => ((LerayHirschDataEvenOf.of_graded LE).chern k).1)
      = fun k => TotalHOf.of K (KGen.lixN n dd) (2 * k)
          (KGen.lixChernDegOf K n dd hgen (mappingTorus (Vmat n) G circHoriz circHeight) k) := by
  funext k
  obtain ⟨x, hx⟩ := hhomE k
  have hdeg : KGen.lixChernDegOf K n dd hgen (mappingTorus (Vmat n) G circHoriz circHeight) k
      = x := by
    rw [KGen.lixChernDegOf_mappingTorus K n dd hgen hGc hGu LE k]
    exact (congrArg (TotalHOf.component K (KGen.lixN n dd) (2 * k)) hx).trans
      (TotalHOf.component_of K (KGen.lixN n dd) (2 * k) x)
  rw [hdeg]
  exact hx

/-- **The bundle data of Step D mod `p` at the real mapping torus**, over a field `K`.  Every input
of `Gen.realBundleModP_of_split` that is a theorem is discharged; the arguments are the torus data
on the geometric projections, the compact Leray–Hirsch data `LE` and `LV`, the homogeneity of the
Chern classes of `LE`, a unit vector `q`, the normalisation, and the narrowed splitting principle for
the Chern classes of `LE`. -/
def realBundleModP_lixChernDegOf (K : Type) [Field K] (p : ℕ) (hp : 2 ≤ p) (n : ℕ)
    (dd : Fin ℓ → ℕ)
    (T : RealTorusModP n K (KnLix.prY n dd) (KnLix.prS1 n dd) (KnLix.prSodd n dd)
      (sphereTopClassOf K 1 (by omega)) (sphereTopClassOf K (2 * n + 1) (by omega)))
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2)
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x))
    (LE : LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd))
    (hhomE : ∀ k : ℕ, ∃ x : TotalPieceOf K (KGen.lixN n dd) (2 * k),
      ((LerayHirschDataEvenOf.of_graded LE).chern k).1
        = TotalHOf.of K (KGen.lixN n dd) (2 * k) x)
    (LV : LerayHirschGraded
      (projMapOf (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
        (vBundleY n dd)))
      (LH.tautEulerDualK K hgen
        (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
          (vBundleY n dd)))
      (KGen.lixRank n dd))
    (q : ↥(unitVectors (Fin (n + 1))))
    (m : ℤ) (hpY : (p : evenPart K (TopCat.of (baseY dd))) = 0)
    (hm : IsUnit (m : evenPart K (TopCat.of (baseY dd))))
    (hwu : HasSplittingPN p (LerayHirschDataEvenOf.of_graded LE).chern T.PN m) :
    RealBundleModP p dd T (fun k => TotalHOf.of K (KGen.lixN n dd) (2 * k)
      (KGen.lixChernDegOf K n dd hgen (mappingTorus (Vmat n) G circHoriz circHeight) k)) :=
  cast (congrArg (RealBundleModP p dd T)
      (coe_chern_eq_lixChernDegOf K n dd hgen hGc hGu LE hhomE))
    (realBundleModP_of_split hp T (LerayHirschDataEvenOf.of_graded LE).chern hhomE
      (KnLix.evenKunnethSplitOf K n dd) (KnLix.slice n dd southPole q)
      (KnLix.slice_map_prY_map K n dd southPole q)
      (KnLix.slice_map_zClass K n dd southPole q _ _)
      (sliceGenPushOf K n (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective hgen)
      (sliceValue_lixBundleOf K n dd G hGc hGu
        ⟨fun y => (southPole, (q, y)),
          continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩
        q (fun _ => rfl) hgen LE LV)
      m hpY hm hwu)

/-- **The first clause of `NinetyNineProblems.LemmaTwoPowersModPData`**, over `F_p` at every stage:
with `Y j` the base of stage `j`, the geometric projections, and the classes
`γfun j W k = of (2k) (KGen.lixChernDegOf (ZMod p) n (lixDD n j) (hgen j) W k)`, the bundle data exist
for every corner unitary.  `p = 0` on the base and the unit property of the normalisation are
discharged from `Fact p.Prime`. -/
theorem nonempty_realBundleModP_lixChernDegOf_stages (n p : ℕ) [Fact p.Prime]
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
    (hhomE : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ) (hGc : Continuous G)
      (hGu : ∀ x, IsCornerUnitary (Vmat n x) (G x)) (k : ℕ),
      ∃ x : TotalPieceOf (ZMod p) (KGen.lixN n (LIX.Gen.lixDD n j)) (2 * k),
        ((LerayHirschDataEvenOf.of_graded (LE j G hGc hGu)).chern k).1
          = TotalHOf.of (ZMod p) (KGen.lixN n (LIX.Gen.lixDD n j)) (2 * k) x)
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
  fun j G hGc hGu =>
    haveI := nonempty_baseY (LIX.Gen.lixDD n j)
    ⟨realBundleModP_lixChernDegOf (ZMod p) p (Fact.out : p.Prime).two_le n (LIX.Gen.lixDD n j)
      (T j) (hgen j) G hGc hGu (LE j G hGc hGu) (hhomE j G hGc hGu) (LV j) q κ
      (natCast_p_evenPart p _) (isUnit_intCast_evenPart p _ hκ) (hwu j G hGc hGu)⟩

end Gen

#audit_axioms Gen.coe_chern_eq_lixChernDegOf
#audit_axioms Gen.realBundleModP_lixChernDegOf
#audit_axioms Gen.nonempty_realBundleModP_lixChernDegOf_stages

end CharClass
end GroupApproximation

end
