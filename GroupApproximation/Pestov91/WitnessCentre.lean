import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Central elements of the crossed product `LC(X, 𝔽₂) ⋊ ℤ`

The simplicity and LEF steps of Pestov 9.1 both need the witness ring to have no central
elements besides `0` and `1`.  This module proves it for every free minimal action.

* `mul_coeff_eq_of_commute_single_one`: if `c ∈ SkewMonoidAlgebra k G` commutes with every
  `single 1 a`, then `a * c_g = c_g * (g • a)` for each `g`.
* `smul_coeff_one_of_commute_single`: if `c` commutes with `single t 1`, then the coefficient
  at `1` is `t`-invariant.
* `central_zero_or_one_of_free_minimal`: take `k = LC(X, 𝔽₂)` with `X` totally separated and
  `(ofAdd j • f) x = f (τ j x)`.  If `τ` is free, the coefficients at `g ≠ 1` vanish.  If
  `τ` is minimal, the coefficient at `1` is constant.  So a central element is `0` or `1`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation

namespace Pestov91

namespace CrossedProduct

open SkewMonoidAlgebra (single)

section Coefficients

variable {k G : Type*} [Ring k] [Group G] [MulSemiringAction G k]

/-- Commuting with every coefficient: `a * c_g = c_g * (g • a)`. -/
theorem mul_coeff_eq_of_commute_single_one {c : SkewMonoidAlgebra k G}
    (hc : ∀ a : k, single 1 a * c = c * single 1 a) (g : G) (a : k) :
    a * c.coeff g = c.coeff g * g • a := by
  have h := congrArg (fun p : SkewMonoidAlgebra k G => p.coeff g) (hc a)
  simpa only [SkewMonoidAlgebra.coeff_single_one_mul,
    SkewMonoidAlgebra.coeff_mul_single_one] using h

/-- Commuting with `single t 1`: the coefficient at `1` is `t`-invariant. -/
theorem smul_coeff_one_of_commute_single {c : SkewMonoidAlgebra k G} {t : G}
    (hc : single t 1 * c = c * single t 1) :
    t • c.coeff 1 = c.coeff 1 := by
  have h := congrArg (fun p : SkewMonoidAlgebra k G => p.coeff t) hc
  simpa only [SkewMonoidAlgebra.coeff_single_mul, SkewMonoidAlgebra.coeff_mul_single,
    inv_mul_cancel, mul_inv_cancel, one_mul, smul_one, mul_one] using h

end Coefficients

section LocallyConstant

variable {X : Type*} [TopologicalSpace X]
  [MulSemiringAction (Multiplicative ℤ) (LocallyConstant X (ZMod 2))]

/-- **The centre of `LC(X, 𝔽₂) ⋊ ℤ` is `{0, 1}`** for a free minimal action on a
nonempty totally separated space, with `(ofAdd j • f) x = f (τ j x)`. -/
theorem central_zero_or_one_of_free_minimal [TotallySeparatedSpace X] [Nonempty X]
    (τ : ℤ → X → X) (hfree : ∀ j : ℤ, j ≠ 0 → ∀ x, τ j x ≠ x)
    (hmin : ∀ x, Dense (Set.range fun j => τ j x))
    (hσ : ∀ (j : ℤ) (f : LocallyConstant X (ZMod 2)) (x : X),
      (Multiplicative.ofAdd j • f) x = f (τ j x))
    (c : SkewMonoidAlgebra (LocallyConstant X (ZMod 2)) (Multiplicative ℤ))
    (hc : ∀ r : SkewMonoidAlgebra (LocallyConstant X (ZMod 2)) (Multiplicative ℤ),
      r * c = c * r) :
    c = 0 ∨ c = 1 := by
  classical
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne 0 1 (by decide)
  -- Freeness: the coefficient at `ofAdd j`, `j ≠ 0`, vanishes at every point.
  have hzero : ∀ j : ℤ, j ≠ 0 → c.coeff (Multiplicative.ofAdd j) = 0 := by
    intro j hj
    ext y
    obtain ⟨U, hU, hyU, hτU⟩ := exists_isClopen_of_totally_separated (hfree j hj y).symm
    have h := congrArg (fun f : LocallyConstant X (ZMod 2) => f y)
      (mul_coeff_eq_of_commute_single_one (fun a => hc (single 1 a))
        (Multiplicative.ofAdd j) (LocallyConstant.charFn (ZMod 2) hU))
    have h1 : LocallyConstant.charFn (ZMod 2) hU y = 1 :=
      (LocallyConstant.charFn_eq_one (ZMod 2) y hU).mpr hyU
    have h0 : (Multiplicative.ofAdd j • LocallyConstant.charFn (ZMod 2) hU) y = 0 := by
      rw [hσ]
      exact (LocallyConstant.charFn_eq_zero (ZMod 2) _ hU).mpr hτU
    have h' : c.coeff (Multiplicative.ofAdd j) y = 0 := by
      simpa only [LocallyConstant.mul_apply, h1, h0, one_mul, mul_zero] using h
    exact h'
  -- Invariance, then minimality: the coefficient at `1` is constant.
  have hinv : ∀ (j : ℤ) (x : X), c.coeff 1 (τ j x) = c.coeff 1 x := by
    intro j x
    rw [← hσ j (c.coeff 1) x,
      smul_coeff_one_of_commute_single (hc (single (Multiplicative.ofAdd j) 1))]
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hconst : ∀ y, c.coeff 1 y = c.coeff 1 x₀ := by
    intro y
    have hsub : Set.range (fun j => τ j x₀) ⊆ {z | c.coeff 1 z = c.coeff 1 x₀} := by
      rintro _ ⟨j, rfl⟩
      exact hinv j x₀
    exact closure_minimal hsub
      ((c.coeff 1).isLocallyConstant.isClopen_fiber (c.coeff 1 x₀)).isClosed (hmin x₀ y)
  have hne : ∀ g : Multiplicative ℤ, ¬(1 : Multiplicative ℤ) = g → c.coeff g = 0 :=
    fun g hg => hzero (Multiplicative.toAdd g) fun h => hg (congrArg Multiplicative.ofAdd h).symm
  have hv : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
  rcases hv (c.coeff 1 x₀) with h | h
  · refine Or.inl (SkewMonoidAlgebra.ext fun g => ?_)
    show c.coeff g = 0
    by_cases hg : (1 : Multiplicative ℤ) = g
    · subst hg
      ext y
      exact (hconst y).trans h
    · exact hne g hg
  · refine Or.inr (SkewMonoidAlgebra.ext fun g => ?_)
    rw [SkewMonoidAlgebra.one_def, SkewMonoidAlgebra.coeff_single_apply]
    split_ifs with hg
    · subst hg
      ext y
      exact (hconst y).trans h
    · exact hne g hg

end LocallyConstant

end CrossedProduct

end Pestov91

end GroupApproximation
