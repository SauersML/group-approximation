import GroupApproximation.CharClass.ParityEvenStepDClosed
import GroupApproximation.CharClass.SliceVGenerator

/-!
# The even side's last input, stated about `V` and nothing else

`LixSliceValue` is the value of the Chern classes of the *restricted mapping
torus* on the south slice.  That is the shape the assembly needs, and it is not
the shape the remaining theorem will have: the classes of the restriction are the
classes of `V` over the projective base, so the statement anyone would prove
mentions neither the mapping torus, nor the clutching map, nor its two
hypotheses.

This file states that shape, `VSliceValue`, and bridges it.  The bridge is
`cc-steenrod`'s own `LH.chernOf_lixSlice_eq_vBundleY`; everything else in the two
statements already agrees, so nothing here is new mathematics.

## What the comparison found

Against `LixSliceValue`, binder by binder:

* the generators agree — both take `gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))`
  as a parameter, and the bridge passes it through untouched, so the existential
  wrapper at the endpoint applies to either;
* the base space agrees — `KnTwo.YTop (baseY dd)` on both sides;
* the coefficient convention agrees — both are `KnTwo.ChernSliceValue`, whose
  right-hand side is `(sliceClass univ gen dd).coeff q`, so the reciprocal Vieta
  convention of `SliceEsymm` is entirely on the producing side and never crosses
  the interface;
* the rank arguments differ in spelling and cannot matter, being proofs;
* the **index type differs**, `VIdx dd ⊕ VIdx dd` against `VIdx dd`, and so does
  the bundle.  That is the one real gap, and it is exactly what
  `chernOf_lixSlice_eq_vBundleY` closes, through `chernOf_pushforward` and the
  invariance lemma.

So the seam is one `congrArg`, and it is closed here rather than left for the
moment the theorem lands.

## Main declarations

* `VSliceValue` — **the even side's last input**, about `V` alone.
* `lixSliceValue_of_vSliceValue` — the bridge.
* `lemmaTwoHolds_of_vSliceValue` — **`LIX.LemmaTwoHolds` over `cc-thom`'s chain
  and this**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The statement about `V` -/

/-- **The value of the Chern classes of `V` on the projective base.**  Mentions no
mapping torus and no clutching map: `V = 𝟏³ ⊕ H` over `∏_j ℂP^{d_j}` and its
generators, and nothing else. -/
def VSliceValue (dd : Fin ℓ → ℕ)
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))) : Prop :=
  KnTwo.ChernSliceValue (baseY dd)
    (LH.chernOf (vBundleY dd) (lixRank dd) (LH.rank_vBundleY_lixRank dd)
      (LH.one_le_lixRank dd)) gen dd

/-! ## 2. The bridge -/

/-- **The value for `V` gives the value for the restricted mapping torus.**  One
`congrArg` over `cc-steenrod`'s identification of the two, which is where the
change of index type is handled. -/
theorem lixSliceValue_of_vSliceValue (dd : Fin ℓ → ℕ)
    (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd)))
    (hval : VSliceValue dd gen) :
    LixSliceValue dd G hGc hGu gen := by
  intro q
  refine Eq.trans ?_ (hval q)
  exact congrArg
    (fun a : Hmod2 (KnTwo.YTop (baseY dd)) (2 * q) =>
      TotalH.of (KnTwo.YTop (baseY dd)) (2 * q) a)
    (LH.chernOf_lixSlice_eq_vBundleY dd G hGc hGu q)

/-! ## 3. The staged shape, and Lemma 2 -/

/-- **Step D's data at every stage**, over the value statement for `V`.  The
generators are existential and no longer depend on the mapping torus, since
`VSliceValue` does not mention it. -/
def data_of_vSliceValue
    (hval : ∀ j : ℕ, ∃ gen : Fin j → TotalH (KnTwo.YTop (baseY (LIX.lixDD j))),
      VSliceValue (LIX.lixDD j) gen) :
    ∀ j : ℕ,
      ∀ G : baseM (LIX.lixDD j) →
        Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ,
        Continuous G → (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        WuStepDLix (LIX.lixDD j)
          (lixChernOf (lixChern (LIX.lixDD j))
            (mappingTorus Vmat G circHoriz circHeight)) :=
  fun j G hGc hGu =>
    wuStepDLix_of_chernSliceValue (LIX.lixDD j) G hGc hGu (hval j).choose
      (lixSliceValue_of_vSliceValue (LIX.lixDD j) G hGc hGu (hval j).choose
        (hval j).choose_spec)

/-- **Lemma 2 over `cc-thom`'s chain and the value statement for `V`.**  This is
the even side's last input in the shape the theorem proving it will have. -/
theorem lemmaTwoHolds_of_vSliceValue
    (chain : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        ThomChainThom (LIX.lixDD j)
          (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
            (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
            (lixRank (LIX.lixDD j))))
    (hval : ∀ j : ℕ, ∃ gen : Fin j → TotalH (KnTwo.YTop (baseY (LIX.lixDD j))),
      VSliceValue (LIX.lixDD j) gen) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_staged'' chain (data_of_vSliceValue hval)

/-! ## 4. At the named generators -/

/-- **Lemma 2 at `cc-projective`'s generator family.**  `LH.sliceGen dd hdd j` is
the degree-two generator of the `j`-th projective factor pulled back to the base,
and `sliceGen_eq_root` says the lines of `V` over that factor all carry it, so the
slice polynomial sees it with exactly the multiplicity `sliceClass` expects.  It is
the family `cc-steenrod`'s value statement is written at, so this endpoint takes
their theorem with no existential introduction in between.

The positivity of every stage's dimensions is `LIX.lixDD_pos`, a theorem, so it is
not a hypothesis here. -/
theorem lemmaTwoHolds_of_sliceGen
    (chain : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        ThomChainThom (LIX.lixDD j)
          (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
            (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
            (lixRank (LIX.lixDD j))))
    (hval : ∀ j : ℕ,
      VSliceValue (LIX.lixDD j) (LH.sliceGen (LIX.lixDD j) (LIX.lixDD_pos j))) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of_vSliceValue chain (fun j => ⟨_, hval j⟩)

/-! ## 5. The axiom report -/

#print axioms lemmaTwoHolds_of_vSliceValue

#print axioms lemmaTwoHolds_of_sliceGen

end

end CharClass
end GroupApproximation
