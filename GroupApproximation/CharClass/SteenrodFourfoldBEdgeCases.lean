import GroupApproximation.CharClass.SteenrodFourfoldBChainMap

/-!
# The two edges of the chain-map condition, and the interchange

The identity proved so far covers a basis element `e_{i+1} ⊗ σ` of positive
resolution index whose simplex has positive dimension.  Two edges of the source
complex are left, and each is degenerate in its own way.

At resolution index `0` there is no `(1 + t)` half of the source differential, and
correspondingly no cancellation to perform: both blocks contribute nothing but
faces.  At simplex dimension `0` there is no boundary at all, and the value of `B`
itself vanishes whenever the resolution index is positive, because the diagonal of
a point is concentrated in bidegree `(0, 0)`.

Both edges are proved here, and then all three statements are carried through the
middle interchange, where the inner swap becomes the block swap.

## Main results

* `tensorD_compBPreGen_zero` — the identity at resolution index `0`.
* `compBGen_pt_eq_zero` — `B` vanishes on a point in positive index.
* `tensorD_compBGen_chain`, `tensorD_compBGen_zero` — **both, after the
  interchange**, where the action is `cc-cartan`'s block swap.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## Resolution index zero -/

/-- **At index `0`, one basis element.**  Neither block has a `(1 + t)` part: the
left block differentiates a cochain of index `0` and the right block a cochain of
back index `0`, and each of those is faces only. -/
theorem sum_tensorD_compBPre_zero (X : TopCat.{0}) (k M : ℕ) (r : PairIdx X (M + 1)) :
    (∑ p ∈ Finset.range 1,
        tensorD (pairFreeCx X) (pairFreeCx X) k (compBPre X (k + 1) 0 p (M + 1) r))
      = ∑ p ∈ Finset.range 1,
          Finsupp.linearCombination (ZMod 2) (compBPre X k 0 p M) (dGen X (ZMod 2) M r) := by
  rw [Finset.sum_range_one, Finset.sum_range_one]
  obtain ⟨⟨⟨c, d⟩, hcd⟩, ρ, τ⟩ := r
  cases c with
  | zero =>
      cases d with
      | zero => exact absurd hcd (by omega)
      | succ M'' =>
          show tensorD (pairFreeCx X) (pairFreeCx X) k
                (bTerm X (k + 1) 0 (M'' + 1) 0 0 ρ τ)
              = Finsupp.linearCombination (ZMod 2) (compBPre X k 0 0 M)
                  (dLeft X (ZMod 2) M 0 (M'' + 1) hcd ρ τ
                    + dRight X (ZMod 2) M 0 (M'' + 1) hcd ρ τ)
          rw [dLeft_zero, zero_add,
            ← faceR_eq_linearCombination X k 0 M 0 M'' 0 hcd ρ τ,
            tensorD_bTerm, padFourL_eq_zero_of_front rfl, zero_add,
            padFourR_compBPre_zero X k 0 M'' 0 (phiAtDeg X 0 0 ρ) τ]
          rfl
  | succ M' =>
      cases d with
      | zero =>
          show tensorD (pairFreeCx X) (pairFreeCx X) k
                (bTerm X (k + 1) (M' + 1) 0 0 0 ρ τ)
              = Finsupp.linearCombination (ZMod 2) (compBPre X k 0 0 M)
                  (dLeft X (ZMod 2) M (M' + 1) 0 hcd ρ τ
                    + dRight X (ZMod 2) M (M' + 1) 0 hcd ρ τ)
          rw [dRight_zero, add_zero,
            ← faceL_eq_linearCombination X k 0 M M' 0 0 hcd ρ τ,
            tensorD_bTerm, padFourR_eq_zero_of_back rfl, add_zero,
            padFourL_compBPre_zero X k M' 0 ρ
              ((groupRingGen ^ 0) • phiAtDeg X 0 0 τ)]
          rfl
      | succ M'' =>
          show tensorD (pairFreeCx X) (pairFreeCx X) k
                (bTerm X (k + 1) (M' + 1) (M'' + 1) 0 0 ρ τ)
              = Finsupp.linearCombination (ZMod 2) (compBPre X k 0 0 M)
                  (dLeft X (ZMod 2) M (M' + 1) (M'' + 1) hcd ρ τ
                    + dRight X (ZMod 2) M (M' + 1) (M'' + 1) hcd ρ τ)
          rw [map_add, ← faceL_eq_linearCombination X k 0 M M' (M'' + 1) 0 hcd ρ τ,
            ← faceR_eq_linearCombination X k 0 M (M' + 1) M'' 0 hcd ρ τ,
            tensorD_bTerm,
            padFourL_compBPre_zero X k M' (M'' + 1) ρ
              ((groupRingGen ^ 0) • phiAtDeg X (M'' + 1) 0 τ),
            padFourR_compBPre_zero X k (M' + 1) M'' 0 (phiAtDeg X (M' + 1) 0 ρ) τ]
          rfl

/-- **At index `0`.**  The differentiated value is the value at the faces. -/
theorem tensorD_compBPreGen_zero (X : TopCat.{0}) (k M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBPreGen X (k + 1) 0 σ)
      = ∑ jj : Fin (M + 2), compBPreGen X k 0 (faceSimplex X M jj σ) := by
  have hlhs : tensorD (pairFreeCx X) (pairFreeCx X) k (compBPreGen X (k + 1) 0 σ)
      = Finsupp.linearCombination (ZMod 2)
          (fun r => ∑ p ∈ Finset.range 1,
            Finsupp.linearCombination (ZMod 2) (compBPre X k 0 p M) (dGen X (ZMod 2) M r))
          (phiZero X (M + 1) σ) := by
    rw [compBPreGen_eq, map_sum,
      Finset.sum_congr rfl (fun p (_ : p ∈ Finset.range 1) =>
        apply_linearCombination' (tensorD (pairFreeCx X) (pairFreeCx X) k)
          (compBPre X (k + 1) 0 p (M + 1)) (phiZero X (M + 1) σ)),
      sum_linearCombination]
    exact congrArg (fun g => Finsupp.linearCombination (ZMod 2) g (phiZero X (M + 1) σ))
      (funext fun r => sum_tensorD_compBPre_zero X k M r)
  rw [hlhs, ← sum_linearCombination]
  have hstep : ∀ p ∈ Finset.range 1,
      Finsupp.linearCombination (ZMod 2)
          (fun r => Finsupp.linearCombination (ZMod 2) (compBPre X k 0 p M)
            (dGen X (ZMod 2) M r)) (phiZero X (M + 1) σ)
        = ∑ jj : Fin (M + 2),
            Finsupp.linearCombination (ZMod 2) (compBPre X k 0 p M)
              (phiZero X M (faceSimplex X M jj σ)) := by
    intro p _
    rw [← apply_linearCombination'
        (Finsupp.linearCombination (ZMod 2) (compBPre X k 0 p M))
        (dGen X (ZMod 2) M) (phiZero X (M + 1) σ),
      ← dTgt_apply, dTgt_phiZero, map_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun jj _ => (compBPreGen_eq X k 0 _).symm

/-! ## Simplex dimension zero -/

/-- **`B` vanishes on a point in positive resolution index.**  The diagonal of a
point sits in bidegree `(0, 0)`, so one of the two cochains is asked for a
positive index it cannot carry. -/
theorem compBPreGen_pt_eq_zero (X : TopCat.{0}) (k i : ℕ) (σ : singularSimplices X 0)
    (hi : 0 < i) : compBPreGen X k i σ = 0 := by
  rw [compBPreGen_eq, phiZero_degree_zero]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hlc : Finsupp.linearCombination (ZMod 2) (compBPre X k i p 0)
      (Finsupp.single (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) 1)
      = compBPre X k i p 0 (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) := by
    simp
  rw [hlc]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · rw [hp]
    exact bTerm_back_pt X k (0 + 0) (0 + (i - 0)) 0 (i - 0) σ σ (by omega)
  · exact bTerm_front_pt X k (0 + p) (0 + (i - p)) p (i - p) σ σ hp

theorem compBGen_pt_eq_zero (X : TopCat.{0}) (k i : ℕ) (σ : singularSimplices X 0)
    (hi : 0 < i) : compBGen X k i σ = 0 := by
  rw [compBGen_eq_midSwap, compBPreGen_pt_eq_zero X k i σ hi]
  exact map_zero _

/-! ## Through the interchange -/

/-- **The chain-map identity for `B` itself**, at positive index and positive
dimension.  The interchange carries the inner swap to `cc-cartan`'s block swap,
which is the action the fourfold carries. -/
theorem tensorD_compBGen_chain (X : TopCat.{0}) (k i M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) (i + 1) σ)
      = (compBGen X k i σ + tenSwap (pairFreeCx X) k (compBGen X k i σ))
        + ∑ jj : Fin (M + 2), compBGen X k (i + 1) (faceSimplex X M jj σ) := by
  rw [tensorD_compBGen_eq, tensorD_compBPreGen, map_add, map_add, midSwap_innerSwap,
    map_sum,
    Finset.sum_congr rfl (fun jj (_ : jj ∈ Finset.univ) =>
      (compBGen_eq_midSwap X k (i + 1) (faceSimplex X M jj σ)).symm),
    ← compBGen_eq_midSwap]

/-- **The chain-map identity for `B` itself**, at index `0`. -/
theorem tensorD_compBGen_zero (X : TopCat.{0}) (k M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) 0 σ)
      = ∑ jj : Fin (M + 2), compBGen X k 0 (faceSimplex X M jj σ) := by
  rw [tensorD_compBGen_eq, tensorD_compBPreGen_zero, map_sum]
  exact Finset.sum_congr rfl fun jj _ =>
    (compBGen_eq_midSwap X k 0 (faceSimplex X M jj σ)).symm

end

end Steenrod
end CharClass
end GroupApproximation
