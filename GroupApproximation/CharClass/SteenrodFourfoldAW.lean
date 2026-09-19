import GroupApproximation.CharClass.SteenrodChainMapNat

/-!
# `Φ₀`, the Alexander–Whitney diagonal

Both composites of the Cartan comparison are built out of `Φ₀`, the value of
Steenrod's diagonal at `W`-index `0`:

```text
Φ₀(σ) = Φ(e₀ ⊗ σ) = ∑_{a+b=n} (front a-face of σ) ⊗ (back b-face of σ).
```

Everything about it is already proved one level down.  It is a chain map on the
nose — no `(1 + T)` correction — because that is the `i = 0` end of the boundary
identity, where the two low terms run over the single empty cut set and vanish;
that is `chainmap_case_last`.  Its naturality is `steenrodDiag_naturality`
transported through `cellPair`.  And on a `0`-simplex it is the literal `x ⊗ x`,
which is the degree-zero normalisation both composites have to satisfy.

So this file introduces one definition and spends already-green results on it.

## Main results

* `phiZero`, `awDiag` — the diagonal on a simplex, and its linear extension.
* `dTgt_phiZero`, `dTgt_awDiag` — **`Φ₀` is a chain map.**
* `phiZero_naturality` — it is natural in the space.
* `phiZero_degree_zero` — on a `0`-simplex it is `x ⊗ x`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The diagonal -/

/-- **The Alexander–Whitney diagonal** of a single simplex: `Φ(e₀ ⊗ σ)`, the sum
over bidegrees of the front face against the back face. -/
def phiZero (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) : PairIdx X n →₀ ZMod 2 :=
  ∑ a ∈ Finset.range (n + 1), phiCell X n 0 a (n - a) σ

/-- `Φ₀` is the published diagonal at `W`-index `0`, which in the "index by the
simplex degree" convention is the top index. -/
theorem phiPair_last (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (Fin.last n).val) :
    phiPair X n ⟨Fin.last n, σ⟩ = phiZero X n σ := by
  rw [phiPair_eq X n (Fin.last n) σ]
  unfold phiZero
  exact Finset.sum_congr rfl fun a _ => phiCell_congr_i n a (n - a) σ (by simp)

/-- `Φ₀` extended linearly to chains. -/
noncomputable def awDiag (X : TopCat.{0}) (n : ℕ) :
    (singularSimplices X n →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx X n →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (phiZero X n)

theorem awDiag_single (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) (c : ZMod 2) :
    awDiag X n (Finsupp.single σ c) = c • phiZero X n σ := by
  unfold awDiag
  simp

theorem awDiag_single_one (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    awDiag X n (Finsupp.single σ 1) = phiZero X n σ := by
  rw [awDiag_single]
  exact one_smul _ _

/-! ## 2. `Φ₀` is a chain map -/

/-- **The Alexander–Whitney diagonal is a chain map on the nose.**  There is no
`(1 + T)` correction, because at cut size zero the two low terms of the master
identity run over `cutIndex 0 = {∅}` and vanish. -/
theorem dTgt_phiZero (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (n + 1)) :
    dTgt X (ZMod 2) n (phiZero X (n + 1) σ)
      = ∑ jj : Fin (n + 2), phiZero X n (faceSimplex X n jj σ) := by
  unfold phiZero
  rw [dTgt_phiSum n 0 σ]
  exact chainmap_case_last n n 0 0 rfl rfl σ

theorem dTgt_awDiag (X : TopCat.{0}) (n : ℕ)
    (z : singularSimplices X (n + 1) →₀ ZMod 2) :
    dTgt X (ZMod 2) n (awDiag X (n + 1) z) = awDiag X n (bdU (ZMod 2) X n z) := by
  classical
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, map_add]
  · intro σ c
    have hs : (Finsupp.single σ c : singularSimplices X (n + 1) →₀ ZMod 2)
        = c • Finsupp.single σ (1 : ZMod 2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, map_smul, map_smul]
    refine congrArg (fun w => c • w) ?_
    rw [awDiag_single_one, dTgt_phiZero, bdU_single, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (awDiag_single_one X n (faceSimplex X n i σ)).symm

/-! ## 3. Naturality -/

theorem pairPushLin_cellPair {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ)
    (z : tensorTwo X a b) :
    pairPushLin X Y f k (cellPair X k a b z)
      = cellPair Y k a b
          (Finsupp.mapDomain (Prod.map (pushSimplex f a) (pushSimplex f b)) z) := by
  by_cases h : a + b = k
  · rw [cellPair_of_eq h, cellPair_of_eq h]
    unfold pairPushLin
    rw [Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    rfl
  · rw [cellPair_of_ne h, cellPair_of_ne h]
    exact map_zero _

theorem pairPushLin_phiCell {X Y : TopCat.{0}} (f : X ⟶ Y) (k i a b : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    pairPushLin X Y f k (phiCell X k i a b σ) = phiCell Y k i a b (pushSimplex f N σ) := by
  unfold phiCell
  rw [pairPushLin_cellPair, steenrodDiag_naturality]

/-- **`Φ₀` is natural in the space.** -/
theorem phiZero_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) :
    pairPushLin X Y f n (phiZero X n σ) = phiZero Y n (pushSimplex f n σ) := by
  unfold phiZero
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => pairPushLin_phiCell f n 0 a (n - a) σ

/-! ## 4. The degree-zero value -/

/-- **On a `0`-simplex the diagonal is the literal `x ⊗ x`.**  This is the
normalisation both composites of the comparison have to match. -/
theorem phiZero_degree_zero (X : TopCat.{0}) (x : singularSimplices X 0) :
    phiZero X 0 x = Finsupp.single (⟨⟨(0, 0), rfl⟩, (x, x)⟩ : PairIdx X 0) 1 := by
  unfold phiZero
  rw [Finset.sum_range_one]
  show cellPair X 0 0 0 (steenrodDiag 0 0 0 x) = _
  rw [steenrodDiag_degree_zero x, cellPair_single_one]
  exact padIdx_of_eq (show 0 + 0 = 0 from rfl) (x, x)

end

end Steenrod
end CharClass
end GroupApproximation
