import GroupApproximation.CharClass.LemmaTwoStepDPinned
import GroupApproximation.CharClass.CohomologyLIXHsliceSouth
import GroupApproximation.CharClass.LIXChernSliceValueBridge
import GroupApproximation.CharClass.LemmaTwoStaged

/-!
# Step D's data over one hypothesis, and Lemma 2 over two

Every field of Step D's data at the mapping torus is discharged except the value of
the Chern classes on the slice.  This file does that assembly, so the even side of
Lemma 2 rests on a single named property of `V` over the projective base.

* `S` is `cc-projective`'s `lixChernSplit`, forced rather than chosen.
* `hsplit` is this lane's `Wu.hasSplitting_lix`.
* `hslice` is `cc-cohom-api`'s `hslice_of_chernSliceValue_south` over
  `cc-steenrod`'s `ChernSliceValue`.

## The generators are not a choice

`ChernSliceValue` is stated against whichever generators are named, so a consumer
free to pick them can produce a datum that typechecks and a hypothesis nothing
discharges.  That is the seam `cc-lix-odd` closed one level out for the splitting,
and it is the same seam here.

Pinning the generators would need a canonical spelling of the hyperplane classes,
and the lane entitled to name them is the one proving the value statement, so a
guess here would recreate the trap pointing the other way.  Instead the generators
come **out of** the hypothesis: `lemmaTwoHolds_of_exists_chernSliceValue` asks only
that some generators work and takes the witness itself.  A consumer never chooses,
so cannot choose wrongly.  The explicit form is kept as well, with the generators
and the value in one binder list so that even there they cannot be paired wrongly.

## The slice point

`hslice_of_chernSliceValue_south` names the sphere coordinate through the model
homeomorphism, while `cc-steenrod`'s bridge is stated at `negEThree` directly.  The
coordinate really is free, so the two are reconciled by choosing the point and
moving it, which is `chernSliceValue_congr_point`: a `subst`, so the two spellings
are never asked to coincide.  Rewriting the round trip in place instead would be a
dependent rewrite through `chernOf`'s two proof arguments.

## Main declarations

* `LixSliceValue` — **the one hypothesis**, named.
* `chernSliceValue_congr_point` — moving the slice point.
* `wuStepDLix_of_chernSliceValue` — Step D's data over it.
* `data_of_chernSliceValue`, `data_of_exists_chernSliceValue` — the same in
  `LemmaTwoStaged`'s `data` binder shape.
* `lemmaTwoHolds_of_exists_chernSliceValue` — **`LIX.LemmaTwoHolds` over two
  inputs**, `cc-thom`'s chain and the slice value.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The one hypothesis, named -/

/-- **The value of the Chern classes on the south slice.**  `cc-steenrod`'s bridge
identifies the restricted mapping torus with `V` over the projective base, so this
is a statement about `V` and the generators alone. -/
def LixSliceValue (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))) : Prop :=
  KnTwo.ChernSliceValue (baseY dd)
    (LH.chernOf
      (Bundle.comap
        (lixSliceMap dd _root_.GroupApproximation.CharClass.southPole negEThree)
        (lixBundle G hGc hGu))
      (lixRank dd)
      (fun y => rank_lixBundle G hGc hGu
        (lixSliceMap dd _root_.GroupApproximation.CharClass.southPole negEThree y))
      (LH.one_le_lixRank dd)) gen dd

/-! ## 2. Moving the slice point -/

/-- **The slice value at one point gives it at an equal point.**  Stated with the
rank hypothesis for the whole bundle, as `hslice_of_chernSliceValue_south` states
it, so that both sides derive the restricted rank the same way. -/
theorem chernSliceValue_congr_point (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)) (s : ℕ)
    (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    {u u' : ↥(unitVectors (Fin 3))} (h : u = u')
    (hval : KnTwo.ChernSliceValue (baseY dd)
      (LH.chernOf (Bundle.comap (lixSliceMap dd p1 u) q) s
        (fun y => hs (lixSliceMap dd p1 u y)) hs1) gen dd) :
    KnTwo.ChernSliceValue (baseY dd)
      (LH.chernOf (Bundle.comap (lixSliceMap dd p1 u') q) s
        (fun y => hs (lixSliceMap dd p1 u' y)) hs1) gen dd := by
  subst h
  exact hval

/-! ## 3. Step D's data over the slice value -/

/-- **Step D's data at the mapping torus, over one hypothesis.**  The splitting is
`lixChernSplit`, the splitting principle is `Wu.hasSplitting_lix`, and the slice
identification is `cc-cohom-api`'s bridge fed the slice value at the point
`cc-steenrod`'s own bridge is stated at.

`WuStepDLix` is a structure rather than a proposition, so this and the two staged
forms below are definitions. -/
def wuStepDLix_of_chernSliceValue (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hval : LixSliceValue dd G hGc hGu gen) :
    WuStepDLix dd
      (lixChernOf (lixChern dd) (mappingTorus Vmat G circHoriz circHeight)) := by
  refine WuStepDPinned.toWuStepDLix (G := G) (hGc := hGc) (hGu := hGu)
    (WuStepDSlice.toWuStepDPinned (G := G) (hGc := hGc) (hGu := hGu) ⟨gen, ?_⟩)
  refine hslice_of_chernSliceValue_south dd
    (unitVectorsThreeHomeoSphere negEThree)
    (mappingTorus Vmat G circHoriz circHeight)
    (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
    (lixRank dd) (LH.one_le_lixRank dd) (fun x => rank_lixBundle G hGc hGu x)
    (lixChernOf (lixChern dd) (mappingTorus Vmat G circHoriz circHeight))
    (fun k => lixChernOf_mappingTorus (lixChern dd) hGc hGu k) gen ?_
  exact chernSliceValue_congr_point dd
    _root_.GroupApproximation.CharClass.southPole (lixBundle G hGc hGu)
    (lixRank dd) (fun x => rank_lixBundle G hGc hGu x) (LH.one_le_lixRank dd) gen
    (unitVectorsThreeHomeoSphere.symm_apply_apply negEThree).symm hval

/-! ## 4. The staged shape -/

/-- **Step D's data at every stage**, in `LemmaTwoStaged`'s `data` binder shape,
with the generators named by the consumer.  They are bound together with the value
they are proved for, so no assembly can pair them wrongly. -/
def data_of_chernSliceValue
    (gen : ∀ j : ℕ, Fin j → TotalH (KnTwo.YTop (baseY (LIX.lixDD j))))
    (hval : ∀ (j : ℕ)
      (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      LixSliceValue (LIX.lixDD j) G hGc hGu (gen j)) :
    ∀ j : ℕ,
      ∀ G : baseM (LIX.lixDD j) →
        Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ,
        Continuous G → (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        WuStepDLix (LIX.lixDD j)
          (lixChernOf (lixChern (LIX.lixDD j))
            (mappingTorus Vmat G circHoriz circHeight)) :=
  fun j G hGc hGu =>
    wuStepDLix_of_chernSliceValue (LIX.lixDD j) G hGc hGu (gen j) (hval j G hGc hGu)

/-- **The same with the generators removed from the consumer's hands.**  Only their
existence is asked for, and the witness is taken here, so a consumer cannot supply
generators the value statement was not proved for. -/
def data_of_exists_chernSliceValue
    (hval : ∀ (j : ℕ)
      (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      ∃ gen : Fin j → TotalH (KnTwo.YTop (baseY (LIX.lixDD j))),
        LixSliceValue (LIX.lixDD j) G hGc hGu gen) :
    ∀ j : ℕ,
      ∀ G : baseM (LIX.lixDD j) →
        Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ,
        Continuous G → (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        WuStepDLix (LIX.lixDD j)
          (lixChernOf (lixChern (LIX.lixDD j))
            (mappingTorus Vmat G circHoriz circHeight)) :=
  fun j G hGc hGu =>
    wuStepDLix_of_chernSliceValue (LIX.lixDD j) G hGc hGu
      (hval j G hGc hGu).choose (hval j G hGc hGu).choose_spec

/-! ## 5. Lemma 2 over two inputs -/

/-- **Lemma 2 over two inputs.**  Step C's chain, which is `cc-thom`'s, and the
value of the Chern classes on the slice, which is `cc-steenrod`'s.  Everything else
in the endgame is a theorem. -/
theorem lemmaTwoHolds_of_exists_chernSliceValue
    (chain : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        ThomChainThom (LIX.lixDD j)
          (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
            (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
            (lixRank (LIX.lixDD j))))
    (hval : ∀ (j : ℕ)
      (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      ∃ gen : Fin j → TotalH (KnTwo.YTop (baseY (LIX.lixDD j))),
        LixSliceValue (LIX.lixDD j) G hGc hGu gen) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_staged'' chain (data_of_exists_chernSliceValue hval)

/-! ## 6. The axiom report -/

#print axioms wuStepDLix_of_chernSliceValue

#print axioms lemmaTwoHolds_of_exists_chernSliceValue

end

end CharClass
end GroupApproximation
