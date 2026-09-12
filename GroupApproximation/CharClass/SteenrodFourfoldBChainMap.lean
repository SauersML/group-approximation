import GroupApproximation.CharClass.SteenrodFourfoldBFaces

/-!
# Composite `B` is a chain map

The identity at one basis element is now summed over the basis of the
Alexander--Whitney diagonal.  Three things happen at once, and each is a named
linearity:

* the differential passes into the linear combination, because it is linear;
* the sum over the resolution index passes into the linear combination, because a
  linear combination is additive in the function it combines along;
* the family of faces becomes the differential of the diagonal, because a linear
  combination along a composite is the composite of linear combinations, and the
  diagonal is a chain map.

## Main results

* `sum_linearCombination`, `linearCombination_add_fun` — additivity of a linear
  combination in the function slot.
* `tensorD_compBPreGen` — **the chain-map identity before the interchange.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## Additivity in the function slot -/

/-- A finite sum of linear combinations is the linear combination along the
pointwise sum. -/
theorem sum_linearCombination {α M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    {ι : Type} (s : Finset ι) (f : ι → α → M) (z : α →₀ ZMod 2) :
    (∑ j ∈ s, Finsupp.linearCombination (ZMod 2) (f j) z)
      = Finsupp.linearCombination (ZMod 2) (fun a => ∑ j ∈ s, f j a) z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | add u v hu hv =>
      simp only [map_add]
      rw [Finset.sum_add_distrib, hu, hv]
  | single a c =>
      have h1 : ∀ g : α → M,
          Finsupp.linearCombination (ZMod 2) g (Finsupp.single a c) = c • g a := by
        intro g
        simp
      rw [h1 (fun x => ∑ j ∈ s, f j x), Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => h1 (f j)

/-- The two-term case, which the assembly meets directly. -/
theorem linearCombination_add_fun {α M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (A B : α → M) (z : α →₀ ZMod 2) :
    Finsupp.linearCombination (ZMod 2) (fun a => A a + B a) z
      = Finsupp.linearCombination (ZMod 2) A z
        + Finsupp.linearCombination (ZMod 2) B z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero]
  | add u v hu hv =>
      simp only [map_add]
      rw [hu, hv]
      abel
  | single a c =>
      have h1 : ∀ g : α → M,
          Finsupp.linearCombination (ZMod 2) g (Finsupp.single a c) = c • g a := by
        intro g
        simp
      rw [h1 (fun x => A x + B x), h1 A, h1 B, smul_add]

/-! ## The two definitions, as equations -/

theorem compBPreGen_eq (X : TopCat.{0}) (k i : ℕ) {N : ℕ} (σ : singularSimplices X N) :
    compBPreGen X k i σ
      = ∑ p ∈ Finset.range (i + 1),
          Finsupp.linearCombination (ZMod 2) (compBPre X k i p N) (phiZero X N σ) := rfl

theorem dTgt_apply (X : TopCat.{0}) (k : ℕ) (z : PairIdx X (k + 1) →₀ ZMod 2) :
    dTgt X (ZMod 2) k z = Finsupp.linearCombination (ZMod 2) (dGen X (ZMod 2) k) z := rfl

/-! ## The chain-map identity -/

/-- **Composite `B` is a chain map, before the interchange.**  The differentiated
value at `e_{i+1} ⊗ σ` is the value at `e_i ⊗ σ`, plus its inner swap, plus the
values at `e_{i+1} ⊗ ∂σ`. -/
theorem tensorD_compBPreGen (X : TopCat.{0}) (k i M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBPreGen X (k + 1) (i + 1) σ)
      = (compBPreGen X k i σ + innerSwapFour X k (compBPreGen X k i σ))
        + ∑ jj : Fin (M + 2), compBPreGen X k (i + 1) (faceSimplex X M jj σ) := by
  -- the level-`i` sum, as a single function of the basis
  set S : PairIdx X (M + 1) → (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
    fun r => ∑ p ∈ Finset.range (i + 1), compBPre X k i p (M + 1) r with hS
  -- the face family, as a single function of the basis
  set F : PairIdx X (M + 1) → (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
    fun r => ∑ p ∈ Finset.range (i + 1 + 1),
      Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M) (dGen X (ZMod 2) M r)
    with hF
  -- the differential passes into the combination, and the index sum with it
  have hlhs : tensorD (pairFreeCx X) (pairFreeCx X) k (compBPreGen X (k + 1) (i + 1) σ)
      = Finsupp.linearCombination (ZMod 2)
          (fun r => (S r + innerSwapFour X k (S r)) + F r) (phiZero X (M + 1) σ) := by
    rw [compBPreGen_eq, map_sum,
      Finset.sum_congr rfl (fun p (_ : p ∈ Finset.range (i + 1 + 1)) =>
        apply_linearCombination' (tensorD (pairFreeCx X) (pairFreeCx X) k)
          (compBPre X (k + 1) (i + 1) p (M + 1)) (phiZero X (M + 1) σ)),
      sum_linearCombination]
    exact congrArg (fun g => Finsupp.linearCombination (ZMod 2) g (phiZero X (M + 1) σ))
      (funext fun r => sum_tensorD_compBPre X k i M r)
  -- the level-`i` part is `B` at level `i`
  have hSval : Finsupp.linearCombination (ZMod 2) S (phiZero X (M + 1) σ)
      = compBPreGen X k i σ := by
    rw [hS, ← sum_linearCombination, ← compBPreGen_eq]
  -- the faces are the diagonal of the boundary
  have hFval : Finsupp.linearCombination (ZMod 2) F (phiZero X (M + 1) σ)
      = ∑ jj : Fin (M + 2), compBPreGen X k (i + 1) (faceSimplex X M jj σ) := by
    rw [hF, ← sum_linearCombination]
    have hstep : ∀ p ∈ Finset.range (i + 1 + 1),
        Finsupp.linearCombination (ZMod 2)
            (fun r => Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
              (dGen X (ZMod 2) M r)) (phiZero X (M + 1) σ)
          = ∑ jj : Fin (M + 2),
              Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                (phiZero X M (faceSimplex X M jj σ)) := by
      intro p _
      rw [← apply_linearCombination'
          (Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M))
          (dGen X (ZMod 2) M) (phiZero X (M + 1) σ),
        ← dTgt_apply, dTgt_phiZero, map_sum]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    exact Finset.sum_congr rfl fun jj _ => (compBPreGen_eq X k (i + 1) _).symm
  rw [hlhs, linearCombination_add_fun, linearCombination_add_fun,
    ← apply_linearCombination' (innerSwapFour X k) S (phiZero X (M + 1) σ),
    hSval, hFval]

end

end Steenrod
end CharClass
end GroupApproximation
