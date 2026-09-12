import GroupApproximation.CharClass.CartanEvalFunctional

/-!
# The evaluating functional kills boundaries, one factor at a time

The comparison is evaluated against a functional that has to annihilate
boundaries, and that is where the cocycle condition on the two classes enters.
This file proves it for one factor: pairing a cochain against the boundary of a
chain is pairing its coboundary against the chain, so a cocycle pairs to zero.

The fourfold statement is then this one applied in each of the four slots, since
the functional is a product over the slots and the differential of the fourfold
is the sum of the four per-factor boundaries.

Everything is stated through `evAt`, the extension of a cochain to every degree
by zero, so no simplex is transported.  The alternating signs of the coboundary
formula collapse because `-1 = 1` in `F₂`.

## Main results

* `sum_evAt_face` — summing a cochain over the faces is evaluating its
  coboundary.
* `evLin` — the cochain as a functional on chains of a fixed degree.
* `evLin_bdU` — **pairing across the boundary**: `⟨α, ∂w⟩ = ⟨δα, w⟩`.
* `evLin_bdU_of_cocycle` — hence zero on a cocycle.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Summing over the faces -/

@[simp] theorem evAt_zero (X : TopCat.{0}) (p m : ℕ) (σ : singularSimplices X m) :
    evAt X p (0 : singularCochainGroup (ZMod 2) X p) m σ = 0 := by
  unfold evAt
  split_ifs with h
  · show cochainEval p (0 : singularCochainGroup (ZMod 2) X p) _ = 0
    simp [cochainEval]
  · rfl

/-- **Summing a cochain over the faces is evaluating its coboundary.**  The
alternating signs collapse because `-1 = 1` in `F₂`. -/
theorem sum_evAt_face (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ)
    (σ : singularSimplices X (m + 1)) :
    ∑ j : Fin (m + 2), evAt X p α m (faceSimplex X m j σ)
      = evAt X (p + 1) (cochainCoboundary (ZMod 2) X p α) (m + 1) σ := by
  by_cases h : m = p
  · subst h
    rw [evAt_self, cochainCoboundary_eval]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evAt_self, show (-1 : ZMod 2) = 1 from by decide, one_pow, one_mul]
  · rw [evAt_of_ne X (p + 1) _ (m + 1) (by omega) σ]
    exact Finset.sum_eq_zero fun j _ => evAt_of_ne X p α m h _

/-! ## 2. The cochain as a functional on chains -/

/-- A cochain of degree `p`, as a functional on the chains of degree `m`: zero
unless the degrees agree. -/
noncomputable def evLin (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ) :
    (singularSimplices X m →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (evAt X p α m)

@[simp] theorem evLin_single (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ) (σ : singularSimplices X m)
    (c : ZMod 2) : evLin X p α m (Finsupp.single σ c) = c * evAt X p α m σ := by
  unfold evLin
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-! ## 3. Pairing across the boundary -/

/-- **Pairing a cochain against a boundary is pairing its coboundary against the
chain.** -/
theorem evLin_bdU (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ)
    (w : singularSimplices X (m + 1) →₀ ZMod 2) :
    evLin X p α m (bdU (ZMod 2) X m w)
      = evLin X (p + 1) (cochainCoboundary (ZMod 2) X p α) (m + 1) w := by
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single σ c =>
      have hs : (Finsupp.single σ c : singularSimplices X (m + 1) →₀ ZMod 2)
          = c • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, map_smul, bdU_single, map_sum]
      refine congrArg (fun z => c • z) ?_
      rw [evLin_single, one_mul, ← sum_evAt_face]
      exact Finset.sum_congr rfl fun j _ => by rw [evLin_single, one_mul]

/-- **A cocycle pairs to zero against every boundary.** -/
theorem evLin_bdU_of_cocycle (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α = 0) (m : ℕ)
    (w : singularSimplices X (m + 1) →₀ ZMod 2) :
    evLin X p α m (bdU (ZMod 2) X m w) = 0 := by
  rw [evLin_bdU, hα]
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add u v hu hv => rw [map_add, hu, hv, add_zero]
  | single σ c => rw [evLin_single, evAt_zero, mul_zero]

end

end GroupApproximation.CharClass
