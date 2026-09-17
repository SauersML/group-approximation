import GroupApproximation.BooneHigman.Metabelian.CharPHost.Carry
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Choose

/-!
# The carry lemma for affine pairs (lane bh-met-01)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4
("Divisibility"): for `(g, b) ∈ R^n ⋊ Γ`, a first-level vertex `(e, α)` with `e ∈ F_p^n`, and
`c = g(0, α) e + b(0, α)`,

  `σ_α(g) e + σ_α(b) = c + s_0 w`   for some `w ∈ R^n`.

This is the entrywise carry lemma `carrySubst_exists` applied to the polynomial entries of
`g e + b` (the entries of `e` are constants, fixed by `σ_α` and by evaluation).  The vector `w` is
the translation part of the state of `(g, b)` at `(e, α)`.

Main declaration: `exists_carrySubst_mulVec_add`, and its char-`p` form `charPCarry_affine`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost

open MvPolynomial Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- **Carry lemma for affine pairs**: `σ_α(g) e + σ_α(b) = c + s_0 w` with
`c = g(0, α) e + b(0, α)` and some polynomial vector `w`. -/
theorem exists_carrySubst_mulVec_add {m : Type*} [Fintype m] (i₀ : ι) (α : ι → R)
    (g : Matrix m m (MvPolynomial ι R)) (b : m → MvPolynomial ι R) (e : m → R) :
    ∃ w : m → MvPolynomial ι R, ∀ j,
      (g.map (carrySubst i₀ α) *ᵥ fun k => C (e k)) j + carrySubst i₀ α (b j) =
        C ((g.map (eval (carryBase i₀ α)) *ᵥ e) j + eval (carryBase i₀ α) (b j)) +
          X i₀ * w j := by
  have key : ∀ j, ∃ Q, carrySubst i₀ α ((g *ᵥ fun k => C (e k)) j + b j) =
      C (eval (carryBase i₀ α) ((g *ᵥ fun k => C (e k)) j + b j)) + X i₀ * Q :=
    fun j => carrySubst_exists i₀ α _
  choose w hw using key
  refine ⟨w, fun j => ?_⟩
  have hσ : carrySubst i₀ α ((g *ᵥ fun k => C (e k)) j + b j) =
      (g.map (carrySubst i₀ α) *ᵥ fun k => C (e k)) j + carrySubst i₀ α (b j) := by
    simp only [map_add, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
      MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  have hev : eval (carryBase i₀ α) ((g *ᵥ fun k => C (e k)) j + b j) =
      (g.map (eval (carryBase i₀ α)) *ᵥ e) j + eval (carryBase i₀ α) (b j) := by
    simp only [map_add, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
      MvPolynomial.eval_C]
  rw [← hσ, ← hev]
  exact hw j

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.exists_carrySubst_mulVec_add

/-- **Char-`p` carry lemma for affine pairs** (lane bh-met-01), over `F_p[s_0, ..., s_{k-1}]`:
`σ_α(g) e + σ_α(b) = g(0, α) e + b(0, α) + s_0 w` for some `w ∈ F_p[s]^n`. -/
theorem charPCarry_affine (p k n : ℕ) [NeZero k] (α : Fin k → ZMod p)
    (g : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) (ZMod p)))
    (b : Fin n → MvPolynomial (Fin k) (ZMod p)) (e : Fin n → ZMod p) :
    ∃ w : Fin n → MvPolynomial (Fin k) (ZMod p), ∀ j,
      (g.map (charPSubst p k α) *ᵥ fun k => C (e k)) j + charPSubst p k α (b j) =
        C ((g.map (eval (carryBase (0 : Fin k) α)) *ᵥ e) j +
          eval (carryBase (0 : Fin k) α) (b j)) + X (0 : Fin k) * w j :=
  exists_carrySubst_mulVec_add (0 : Fin k) α g b e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.charPCarry_affine

end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation
