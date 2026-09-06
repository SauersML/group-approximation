import GroupApproximation.CharClass.SteenrodFourfoldBChain
import GroupApproximation.CharClass.SteenrodChainMapNat
import GroupApproximation.CharClass.CartanMidFourNat

/-!
# Naturality of the second composite

`B` is natural in the space because everything it is built from is: the diagonal
at a fixed index is natural, the totalised decomposable of the fourfold is
natural because `tenElt` is, and the group ring acts through a map that commutes
with pushing simplices forward.

This file proves it for `compBPre`, the value before the middle interchange.
Crossing the interchange is `cc-cartan`'s `midSwap` naturality, which is a
statement about their object and is the only step not proved here.

## Main results

* `phiAtDeg_naturality` — the diagonal at a fixed index and total degree.
* `tenHom_padFour` — a totalised decomposable pushes forward factorwise.
* `compBPre_naturality` — **one term of `B` is natural**, before the interchange.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The diagonal at a fixed index is natural -/

theorem phiAtDeg_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (m j N : ℕ)
    (σ : singularSimplices X N) :
    pairPushLin X Y f m (phiAtDeg X m j σ) = phiAtDeg Y m j (pushSimplex f N σ) := by
  unfold phiAtDeg
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => pairPushLin_phiCell f m j a (m - a) σ

/-- The same, phrased against `cc-cartan`'s pushforward on the pair complex. -/
theorem pairHom_phiAtDeg {X Y : TopCat.{0}} (f : X ⟶ Y) (m j N : ℕ)
    (σ : singularSimplices X N) :
    (pairHom f).f m (phiAtDeg X m j σ) = phiAtDeg Y m j (pushSimplex f N σ) := by
  rw [pairHom_f_eq]
  exact phiAtDeg_naturality f m j N σ

/-- The pushforward on the pair complex is linear over the group ring. -/
theorem pairHom_smul {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ) (c : GroupRingZ2)
    (w : PairIdx X m →₀ ZMod 2) :
    (pairHom f).f m (c • w) = c • (pairHom f).f m w := by
  rw [pairHom_f_eq]
  exact pairPushLin_smul f m c w

/-! ## 2. A totalised decomposable pushes forward factorwise -/

theorem tenHom_padFour {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    tenHom (pairHom f) (pairHom f) k (padFour X k a b u v)
      = padFour Y k a b ((pairHom f).f a u) ((pairHom f).f b v) := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h, padFour_of_eq h]
    exact tenHom_tenElt (pairHom f) (pairHom f) k a b h u v
  · rw [padFour_of_ne h, padFour_of_ne h]
    exact map_zero (tenHom (pairHom f) (pairHom f) k)

/-! ## 3. One term of `B` is natural -/

/-- **Naturality of one term of `B`, before the middle interchange.**  The
bidegree of the basis element is untouched by the pushforward, so both factors
move independently and the degrees on the two sides agree on the nose. -/
theorem compBPre_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k i p N : ℕ)
    (r : PairIdx X N) :
    tenHom (pairHom f) (pairHom f) k (compBPre X k i p N r)
      = compBPre Y k i p N (pairIdxPush f N r) := by
  show tenHom (pairHom f) (pairHom f) k
      (padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
        (phiAtDeg X (r.1.val.1 + p) p r.2.1)
        ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2))
    = padFour Y k (r.1.val.1 + p) (r.1.val.2 + (i - p))
        (phiAtDeg Y (r.1.val.1 + p) p (pushSimplex f r.1.val.1 r.2.1))
        ((groupRingGen ^ p)
          • phiAtDeg Y (r.1.val.2 + (i - p)) (i - p) (pushSimplex f r.1.val.2 r.2.2))
  rw [tenHom_padFour, pairHom_phiAtDeg, pairHom_smul, pairHom_phiAtDeg]

/-! ## 4. Naturality of `B` itself

Crossing the middle interchange is `cc-cartan`'s `midSwap_pairHom`.  With it the
rest is bookkeeping: the term is natural, the diagonal `Φ₀` whose basis the sum
runs over is natural, and a linear combination along a pushed-forward index is a
linear combination of the pushed-forward summand. -/

theorem compBTerm_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k i p N : ℕ)
    (r : PairIdx X N) :
    tenHom (pairHom f) (pairHom f) k (compBTerm X k i p N r)
      = compBTerm Y k i p N (pairIdxPush f N r) := by
  show tenHom (pairHom f) (pairHom f) k
      (midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k
        (compBPre X k i p N r)) = _
  rw [midSwap_pairHom, compBPre_naturality]
  rfl

theorem compBGen_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k i N : ℕ)
    (σ : singularSimplices X N) :
    tenHom (pairHom f) (pairHom f) k (compBGen X k i σ)
      = compBGen Y k i (pushSimplex f N σ) := by
  have hz : phiZero Y N (pushSimplex f N σ)
      = Finsupp.mapDomain (pairIdxPush f N) (phiZero X N σ) :=
    (phiZero_naturality f N σ).symm
  unfold compBGen
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hfun : (fun r : PairIdx X N =>
        tenHom (pairHom f) (pairHom f) k (compBTerm X k i p N r))
      = fun r : PairIdx X N => compBTerm Y k i p N (pairIdxPush f N r) :=
    funext fun r => compBTerm_naturality f k i p N r
  rw [apply_linearCombination', hfun, hz, Finsupp.linearCombination_mapDomain]
  rfl

/-- **The second composite is natural in the space.** -/
theorem compB_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (y : WTensorSMod X k) :
    (fourHom f).f k (compB X k y)
      = compB Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add]
    exact (map_add (compB Y k) _ _).symm
  · intro b c
    have hs : (Finsupp.single b c : WTensorSMod X k)
        = c • Finsupp.single b (1 : GroupRingZ2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, fourHom_smul, map_smul, map_smul]
    refine congrArg (fun w => c • w) ?_
    rw [compB_single, one_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      compB_single, one_smul]
    exact compBGen_naturality f k (k - b.1.val) b.1.val
      ((simplexEquiv X b.1.val).symm b.2)

end

end Steenrod
end CharClass
end GroupApproximation
