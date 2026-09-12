import GroupApproximation.CharClass.SliceTorusOf
import GroupApproximation.CharClass.LerayHirschCompactClosedOf
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.Meta.AxiomGuard

/-!
# The slice field at the real mapping torus over a field, with Leray–Hirsch discharged

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm.

`Gen.sliceValue_lixBundleOf` (`SliceTorusOf`) computes the slice value over two Leray–Hirsch
statements over `K`: one for the rank-`n` mapping torus (`LE`), one for `V` pushed along the second
summand of the doubled index (`LV`), both at the dual tautological class of the same generator
`hgen`.  Lane `lx-lhK-b`'s `LH.lerayHirschGraded_compactDualOf` proves Leray–Hirsch over a compact
nonempty base for every nonzero `hgen`, so both are theorems.  The ranks are `lixRank n dd`: the
mapping torus by its trace (`KGen.rank_lixBundle`), and `V` by its trace, which the pushforward
keeps (`LH.rank_pushforward`).

## Main declarations

* `Gen.lerayHirschGraded_lixBundleOf` — Leray–Hirsch for the mapping torus over `K`.
* `Gen.lerayHirschGraded_vBundleY_inrOf` — Leray–Hirsch for `V` pushed along `Sum.inr` over `K`.
* `Gen.sliceValue_lixBundleOf_closed` — **the slice field at the real mapping torus, for every
  nonzero generator, with no Leray–Hirsch hypothesis.**
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH

set_option linter.unusedSectionVars false

namespace Gen

/-- **Leray–Hirsch for the rank-`n` mapping torus over a field**, at the dual tautological class of
any nonzero generator. -/
theorem lerayHirschGraded_lixBundleOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} {dd : Fin ℓ → ℕ}
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2) (hgen0 : hgen ≠ 0) :
    LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd) :=
  LH.lerayHirschGraded_compactDualOf K (KGen.lixBundle n G hGc hGu) (KGen.lixRank n dd)
    (KGen.rank_lixBundle n G hGc hGu) (KGen.one_le_lixRank n dd) hgen hgen0

/-- **Leray–Hirsch for `V` pushed along the second summand, over a field**, at the dual tautological
class of any nonzero generator. -/
theorem lerayHirschGraded_vBundleY_inrOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2) (hgen0 : hgen ≠ 0) :
    LerayHirschGraded
      (projMapOf (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
        (vBundleY n dd)))
      (LH.tautEulerDualK K hgen
        (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
          (vBundleY n dd)))
      (KGen.lixRank n dd) := by
  haveI : Nonempty (baseY dd) := ⟨baseYPoint dd⟩
  exact LH.lerayHirschGraded_compactDualOf K
    (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective (vBundleY n dd))
    (KGen.lixRank n dd)
    (fun y => (LH.rank_pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
      (vBundleY n dd) y).trans (rank_vBundleY n dd y))
    (KGen.one_le_lixRank n dd) hgen hgen0

/-- **The slice field at the real mapping torus, with Leray–Hirsch discharged.**  For every nonzero
generator `hgen`, the Chern classes over `K` of the rank-`n` mapping torus, restricted to the south
polar slice, are the coefficients of `∏ⱼ (1 + hⱼ X)^{dⱼ}`.  Any other Leray–Hirsch proof at the same
class gives the same Chern classes, because `LerayHirschGraded` is a `Prop`. -/
theorem sliceValue_lixBundleOf_closed (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (s : C(baseY dd, ↥sphereOne × baseM n dd)) (q : ↥(unitVectors (Fin (n + 1))))
    (hs : ∀ y, s y = (southPole, ((q, y) : baseM n dd)))
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2) (hgen0 : hgen ≠ 0)
    (k : ℕ) :
    Gen.evenMap K (cmap s)
        ((LerayHirschDataEvenOf.of_graded
          (lerayHirschGraded_lixBundleOf K n G hGc hGu hgen hgen0)).chern k)
      = (sliceClass (Finset.univ : Finset (Fin ℓ))
          (sliceGenPushOf K n (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective hgen)
          dd).coeff k :=
  sliceValue_lixBundleOf K n dd G hGc hGu s q hs hgen
    (lerayHirschGraded_lixBundleOf K n G hGc hGu hgen hgen0)
    (lerayHirschGraded_vBundleY_inrOf K n dd hgen hgen0) k

end Gen

#audit_axioms Gen.lerayHirschGraded_lixBundleOf
#audit_axioms Gen.lerayHirschGraded_vBundleY_inrOf
#audit_axioms Gen.sliceValue_lixBundleOf_closed

end GroupApproximation.CharClass
