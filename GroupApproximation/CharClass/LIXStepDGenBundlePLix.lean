import GroupApproximation.CharClass.LIXStepDGenBundleP
import GroupApproximation.CharClass.LIXStepDGenExpChar

/-!
# The bundle data of Step D mod `p` at every stage of the tower, over `F_p`

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

`Gen.lemmaTwoFor_powers_of_stepC_realModP` (`CharClass/LIXStepDGenReal.lean`) owes, for every stage
`j` and every corner unitary `G`, the bundle data `Gen.RealBundleModP` of the mapping torus of `G`,
and the instance `ExpChar (evenPart K (Y j)) p` at every base.  This file supplies both over
`K = ZMod p` with `Y j = ∏ᵢ ℂP^{dᵢ}`:

* the bundle data at every `j` and `G`, from `Gen.realBundleModP_of_split`, with `p = 0` on `Y j`
  and the unit normalisation discharged from `Fact p.Prime` (`CharClass/LIXStepDGenExpChar.lean`);
* the instance, from `Gen.expChar_evenPart_baseY`.

The remaining inputs are the named ones of `Gen.realBundleModP_of_split`, stage by stage: the
homogeneous even Chern classes, the Künneth split at each torus, the slice section with the slice
value, and the narrowed splitting principle.  Stage `0` is not special anywhere: `lixDD n 0` is the
empty family, the base is a point, and every input is stated for all `j`.

`Gen.realBundleModP_stages_deg` is the same over a **degreewise** family `deg j W k` in degree `2k`:
its classes are literally `k ↦ of (2k) (deg j W k)`, the `γfun` of
`NinetyNineProblems.LemmaTwoPowersModPData`, so no homogeneity input is asked for there.

## Main results

* `Gen.realBundleModP_stages` — **the data binder of `lemmaTwoFor_powers_of_stepC_realModP`**.
* `Gen.evenDeg`, `Gen.realBundleModP_stages_deg`, `Gen.nonempty_realBundleModP_stages_deg` — the
  degreewise forms.
* `Gen.lemmaTwoFor_powers_of_stepC_bundleP` — Lemma 2 for the degree-`k` family at every stage,
  from the Step C half and the named Step D inputs over `F_p`.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open ParityP

namespace Gen

/-- **The bundle data of Step D mod `p` at every stage and every corner unitary**, over `F_p`, with
the base `Y j = ∏ᵢ ℂP^{dᵢ}` of stage `j`.  Its type is the `data` binder of
`Gen.lemmaTwoFor_powers_of_stepC_realModP` at `γfun j W k = ΓE j W k`. -/
def realBundleModP_stages (n p : ℕ) [Fact p.Prime] {N S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ TopCat.of (baseY (LIX.Gen.lixDD n j))} {q₁ : ∀ j, N j ⟶ S₁ j}
    {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf (ZMod p) (S₁ j) 1}
    {σodd : ∀ j, TotalPieceOf (ZMod p) (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (ΓE : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ℕ → evenPart (ZMod p) (N j))
    (hhom : ∀ (j : ℕ) (W : ↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) (k : ℕ),
      ∃ x : TotalPieceOf (ZMod p) (N j) (2 * k),
        (ΓE j W k : TotalHOf (ZMod p) (N j)) = TotalHOf.of (ZMod p) (N j) (2 * k) x)
    (hsplit : ∀ j, EvenKunnethSplitOf n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (s : ∀ j, TopCat.of (baseY (LIX.Gen.lixDD n j)) ⟶ N j)
    (hs : ∀ (j : ℕ) (c : TotalHOf (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j)))),
      TotalHOf.map (ZMod p) (s j) (TotalHOf.map (ZMod p) (pY j) c) = c)
    (hsz : ∀ j, TotalHOf.map (ZMod p) (s j) (zClass (ZMod p) (q₁ j) (qodd j) (σ₁ j) (σodd j)) = 0)
    (gen : ∀ j : ℕ, Fin j → evenPart (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j))))
    (hslice : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) → ∀ q : ℕ,
        evenMap (ZMod p) (s j) (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight) q)
          = (sliceClass Finset.univ (gen j) (LIX.Gen.lixDD n j)).coeff q)
    (κ : ℤ) (hκ : IsUnit (κ : ZMod p))
    (hwu : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
        HasSplittingPN p (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight)) (T j).PN κ) :
    ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
      RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (fun k => (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight) k : TotalHOf (ZMod p) (N j))) :=
  fun j G hGc hGu =>
    haveI := nonempty_baseY (LIX.Gen.lixDD n j)
    realBundleModP_of_split (Fact.out : p.Prime).two_le (T j)
      (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight)) (hhom j _) (hsplit j) (s j) (hs j)
      (hsz j) (gen j) (hslice j G hGc hGu) κ (natCast_p_evenPart p _)
      (isUnit_intCast_evenPart p _ hκ) (hwu j G hGc hGu)

/-- **The even family of a degreewise family**: `k ↦ of (2k) (deg k)`, even by degree. -/
def evenDeg {K : Type} [CommRing K] {N : TopCat.{0}} (deg : ∀ k : ℕ, TotalPieceOf K N (2 * k)) :
    ℕ → evenPart K N :=
  fun k => ⟨TotalHOf.of K N (2 * k) (deg k), TotalHOf.isEven_of K N (even_two_mul k) _⟩

/-- **`Gen.realBundleModP_stages` over a degreewise family.**  The output classes are literally
`k ↦ of (2k) (deg j W k)`, so the link to a top class `deg j W r` is `rfl` and no homogeneity input
is asked for. -/
def realBundleModP_stages_deg (n p : ℕ) [Fact p.Prime] {N S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ TopCat.of (baseY (LIX.Gen.lixDD n j))} {q₁ : ∀ j, N j ⟶ S₁ j}
    {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf (ZMod p) (S₁ j) 1}
    {σodd : ∀ j, TotalPieceOf (ZMod p) (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (deg : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ∀ k : ℕ, TotalPieceOf (ZMod p) (N j) (2 * k))
    (hsplit : ∀ j, EvenKunnethSplitOf n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (s : ∀ j, TopCat.of (baseY (LIX.Gen.lixDD n j)) ⟶ N j)
    (hs : ∀ (j : ℕ) (c : TotalHOf (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j)))),
      TotalHOf.map (ZMod p) (s j) (TotalHOf.map (ZMod p) (pY j) c) = c)
    (hsz : ∀ j, TotalHOf.map (ZMod p) (s j) (zClass (ZMod p) (q₁ j) (qodd j) (σ₁ j) (σodd j)) = 0)
    (gen : ∀ j : ℕ, Fin j → evenPart (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j))))
    (hslice : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) → ∀ q : ℕ,
        evenMap (ZMod p) (s j) (evenDeg (deg j (mappingTorus (Vmat n) G circHoriz circHeight)) q)
          = (sliceClass Finset.univ (gen j) (LIX.Gen.lixDD n j)).coeff q)
    (κ : ℤ) (hκ : IsUnit (κ : ZMod p))
    (hwu : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
        HasSplittingPN p (evenDeg (deg j (mappingTorus (Vmat n) G circHoriz circHeight)))
          (T j).PN κ) :
    ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
      RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (fun k => TotalHOf.of (ZMod p) (N j) (2 * k)
          (deg j (mappingTorus (Vmat n) G circHoriz circHeight) k)) :=
  realBundleModP_stages n p T (fun j W => evenDeg (deg j W)) (fun _ _ _ => ⟨_, rfl⟩) hsplit s hs
    hsz gen hslice κ hκ hwu

/-- **The existence form** of `Gen.realBundleModP_stages_deg`, the shape the endpoint's named
proposition asks for. -/
theorem nonempty_realBundleModP_stages_deg (n p : ℕ) [Fact p.Prime] {N S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ TopCat.of (baseY (LIX.Gen.lixDD n j))} {q₁ : ∀ j, N j ⟶ S₁ j}
    {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf (ZMod p) (S₁ j) 1}
    {σodd : ∀ j, TotalPieceOf (ZMod p) (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (deg : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ∀ k : ℕ, TotalPieceOf (ZMod p) (N j) (2 * k))
    (hsplit : ∀ j, EvenKunnethSplitOf n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (s : ∀ j, TopCat.of (baseY (LIX.Gen.lixDD n j)) ⟶ N j)
    (hs : ∀ (j : ℕ) (c : TotalHOf (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j)))),
      TotalHOf.map (ZMod p) (s j) (TotalHOf.map (ZMod p) (pY j) c) = c)
    (hsz : ∀ j, TotalHOf.map (ZMod p) (s j) (zClass (ZMod p) (q₁ j) (qodd j) (σ₁ j) (σodd j)) = 0)
    (gen : ∀ j : ℕ, Fin j → evenPart (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j))))
    (hslice : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) → ∀ q : ℕ,
        evenMap (ZMod p) (s j) (evenDeg (deg j (mappingTorus (Vmat n) G circHoriz circHeight)) q)
          = (sliceClass Finset.univ (gen j) (LIX.Gen.lixDD n j)).coeff q)
    (κ : ℤ) (hκ : IsUnit (κ : ZMod p))
    (hwu : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
        HasSplittingPN p (evenDeg (deg j (mappingTorus (Vmat n) G circHoriz circHeight)))
          (T j).PN κ) :
    ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
      Nonempty (RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (fun k => TotalHOf.of (ZMod p) (N j) (2 * k)
          (deg j (mappingTorus (Vmat n) G circHoriz circHeight) k))) :=
  fun j G hGc hGu =>
    ⟨realBundleModP_stages_deg n p T deg hsplit s hs hsz gen hslice κ hκ hwu j G hGc hGu⟩

/-- **Lemma 2 for the degree-`k` family at every stage, from the Step C half and the named Step D
inputs over `F_p`.**  At a prime `p ∣ n`: the torus data, the homogeneous even Chern classes, the
Künneth split, the slice section and value, and the narrowed splitting principle at every stage,
together with the Step C half at the top class, give Lemma 2 for every exponent `k` with `p ∤ k`. -/
theorem lemmaTwoFor_powers_of_stepC_bundleP (n p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n)
    (hpn : p ∣ n) {N S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ TopCat.of (baseY (LIX.Gen.lixDD n j))} {q₁ : ∀ j, N j ⟶ S₁ j}
    {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf (ZMod p) (S₁ j) 1}
    {σodd : ∀ j, TotalPieceOf (ZMod p) (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (ΓE : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ℕ → evenPart (ZMod p) (N j))
    (hhom : ∀ (j : ℕ) (W : ↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) (k : ℕ),
      ∃ x : TotalPieceOf (ZMod p) (N j) (2 * k),
        (ΓE j W k : TotalHOf (ZMod p) (N j)) = TotalHOf.of (ZMod p) (N j) (2 * k) x)
    (hsplit : ∀ j, EvenKunnethSplitOf n (ZMod p) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    (s : ∀ j, TopCat.of (baseY (LIX.Gen.lixDD n j)) ⟶ N j)
    (hs : ∀ (j : ℕ) (c : TotalHOf (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j)))),
      TotalHOf.map (ZMod p) (s j) (TotalHOf.map (ZMod p) (pY j) c) = c)
    (hsz : ∀ j, TotalHOf.map (ZMod p) (s j) (zClass (ZMod p) (q₁ j) (qodd j) (σ₁ j) (σodd j)) = 0)
    (gen : ∀ j : ℕ, Fin j → evenPart (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j))))
    (hslice : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) → ∀ q : ℕ,
        evenMap (ZMod p) (s j) (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight) q)
          = (sliceClass Finset.univ (gen j) (LIX.Gen.lixDD n j)).coeff q)
    (κ : ℤ) (hκ : IsUnit (κ : ZMod p))
    (hwu : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ x, IsCornerUnitary (Vmat n x) (G x)) →
        HasSplittingPN p (ΓE j (mappingTorus (Vmat n) G circHoriz circHeight)) (T j).PN κ)
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
        (fun W => (ΓE j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)) : TotalHOf (ZMod p) (N j)))) :
    ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) := by
  haveI : ∀ j : ℕ, ExpChar (evenPart (ZMod p) (TopCat.of (baseY (LIX.Gen.lixDD n j)))) p :=
    fun j => expChar_evenPart_baseY p (LIX.Gen.lixDD n j)
  exact lemmaTwoFor_powers_of_stepC_realModP n p hp.out hn hpn T
    (fun j W k => (ΓE j W k : TotalHOf (ZMod p) (N j)))
    (realBundleModP_stages n p T ΓE hhom hsplit s hs hsz gen hslice κ hκ hwu) hC

end Gen

#audit_axioms Gen.realBundleModP_stages
#audit_axioms Gen.evenDeg
#audit_axioms Gen.realBundleModP_stages_deg
#audit_axioms Gen.nonempty_realBundleModP_stages_deg
#audit_axioms Gen.lemmaTwoFor_powers_of_stepC_bundleP

end CharClass
end GroupApproximation

end
