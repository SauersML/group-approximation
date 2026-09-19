import GroupApproximation.CharClass.SteenrodFourfoldBBranch

/-!
# The junctions, and the two live block splits

Two numbers arrive spelled two ways in the assembly of composite `B`'s chain map
condition, and both are isolated here so that the assembly never normalises
arithmetic in the middle of a rewrite chain.

The front degree arrives as `c + (p + 1)` where the block lemmas want
`c + p + 1`; those are the same term, so `exact` crosses the junction and no
lemma is needed.  The back index arrives as `i + 1 - (p + 1)` where the level-`i`
sum spells it `i - p`; those are *not* the same term, and the number sits inside
the type of a cochain, so the transport has to be a `congrArg` along a genuine
function of the index.  `bBack` is that function -- the back degree and the back
index move together, and the result type does not mention either -- and
`bBack_pred` is the transport.

With the junctions named, each live block of the Leibniz expansion splits into
exactly three pieces: the piece that cancels, the piece that is the inner swap of
the level-`i` summand, and the faces.

## Main results

* `bBack_pred` — **the junction**: `i + 1 - (p + 1)` may be read as `i - p`.
* `innerSwapFour_bTerm` — the swap of a summand, in `padFour` form.
* `bTerm_left_split`, `bTerm_right_split` — **the two live blocks**, each in
  three named pieces.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- The summand of `B`, unfolded. -/
theorem bTerm_eq (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    bTerm X k a b p q ρ τ
      = padFour X k a b (phiAtDeg X a p ρ) ((groupRingGen ^ p) • phiAtDeg X b q τ) := rfl

/-! ## The back junction -/

/-- The summand read as a function of its back index alone, the back degree
moving with it.  The result type does not mention the index, so `congrArg`
crosses any equation between two spellings of it. -/
def bBack (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (q : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  bTerm X k a (d + q) p q ρ τ

theorem bBack_eq (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (q : ℕ) :
    bBack X k a p ρ τ q
      = padFour X k a (d + q) (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (d + q) q τ) := rfl

/-- **The junction**, as a transport along an equation between two spellings of
the back index, with every degree a free parameter. -/
theorem bBack_congr (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) {q q' : ℕ} (h : q = q') :
    bBack X k a p ρ τ q = bBack X k a p ρ τ q' :=
  congrArg (bBack X k a p ρ τ) h

/-- The junction the assembly actually meets: at summand index `p + 1` of the
level-`i + 1` sum, the back index is the level-`i` sum's back index at `p`. -/
theorem bBack_pred (X : TopCat.{0}) (k a p i : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    bBack X k a p ρ τ (i + 1 - (p + 1)) = bBack X k a p ρ τ (i - p) :=
  bBack_congr X k a p ρ τ (Nat.succ_sub_succ i p)

/-! ## The swap of a summand -/

/-- Swapping a summand swaps both ends; on the right end the swap is absorbed
into the power of the generator, so only the left end still carries one. -/
theorem innerSwapFour_bTerm (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    innerSwapFour X k (bTerm X k a b p q ρ τ)
      = padFour X k a b (swapEnd X a (phiAtDeg X a p ρ))
          ((groupRingGen ^ (p + 1)) • phiAtDeg X b q τ) := by
  rw [bTerm_eq, tenHom_swapHom_padFour, swapEnd_smul_pow]

/-! ## The two live blocks -/

/-- **The left block at a successor index**, in three pieces: the piece carrying
one power of the generator too many, which is what cancels; the inner swap of the
level-`i` summand; and the faces of the front simplex. -/
theorem bTerm_left_split (X : TopCat.{0}) (k M' p' b q : ℕ) {d : ℕ}
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) :
    padFourL X k (M' + 1 + p' + 1) b (phiAtDeg X (M' + 1 + p' + 1) (p' + 1) ρ)
        ((groupRingGen ^ (p' + 1)) • phiAtDeg X b q τ)
      = (padFour X k (M' + 1 + p') b (phiAtDeg X (M' + 1 + p') p' ρ)
              ((groupRingGen ^ (p' + 1)) • phiAtDeg X b q τ)
            + innerSwapFour X k (bTerm X k (M' + 1 + p') b p' q ρ τ))
          + padFour X k (M' + 1 + p') b
              (∑ jj : Fin (M' + 2),
                phiAtDeg X (M' + 1 + p') (p' + 1) (faceSimplex X M' jj ρ))
              ((groupRingGen ^ (p' + 1)) • phiAtDeg X b q τ) := by
  rw [padFourL_compBPre_succ, padFour_split3_left, innerSwapFour_bTerm]

/-- **The right block at a successor index**, in three pieces: the level-`i`
summand itself; the piece carrying one power of the generator too many, which is
what the left block's first piece cancels against; and the faces of the back
simplex. -/
theorem bTerm_right_split (X : TopCat.{0}) (k a M'' q' p : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) :
    padFourR X k a (M'' + 1 + q' + 1) (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X (M'' + 1 + q' + 1) (q' + 1) τ)
      = (bTerm X k a (M'' + 1 + q') p q' ρ τ
            + padFour X k a (M'' + 1 + q') (phiAtDeg X a p ρ)
                ((groupRingGen ^ (p + 1)) • phiAtDeg X (M'' + 1 + q') q' τ))
          + padFour X k a (M'' + 1 + q') (phiAtDeg X a p ρ)
              ((groupRingGen ^ p) •
                ∑ jj : Fin (M'' + 2),
                  phiAtDeg X (M'' + 1 + q') (q' + 1) (faceSimplex X M'' jj τ)) := by
  rw [padFourR_compBPre_succ, padFour_split3_right, bTerm_eq, smul_pow_swapEnd]

end

end Steenrod
end CharClass
end GroupApproximation
