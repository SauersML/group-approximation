import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Group
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Abel

/-!
# Output letters and states of the char-zero host (lane bh-met-09)

Research claim: at the letter `(e, a) ∈ F_p^n × F_p^k`, the affine map `(g, b)` outputs
`(c, a)` with `c = π (g(a) e + b(a))`, and moves to the state
`(σ_a g, (σ_a g e + σ_a b - c) / p)`.

Here `z x ℓ = g e + b - c` (with digit vectors cast to constant polynomials), the digit of every
entry of `z x ℓ` vanishes (`dig_z`), so `σ_a (z x ℓ) = p · stateVec x ℓ` (`sigmaZ_z`).

**Route (cocycle rules).**
* `outDigit_mul`: `c(xy, ℓ) = c(x, ℓ')` for `ℓ' = letter y ℓ`, since
  `g_x c_y + b_x = (g_x g_y e + g_x b_y + b_x) - g_x z(y, ℓ)` and `g_x z(y, ℓ)` has zero digits;
* `z_mul`: `z(xy, ℓ) = z(x, ℓ') + g_x z(y, ℓ)` (abel);
* `stateVec_mul`, `stateG_mul`: `stateG (x y) ℓ = stateG x ℓ' * stateG y ℓ`, by cancelling `p`
  (`A` is a char-zero domain) after applying `σ_a` to `z_mul`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial
open scoped Matrix

/-- The letters `F_p^n × F_p^k`. -/
abbrev Letter (p n k : ℕ) : Type := (Fin n → ZMod p) × (Fin k → ZMod p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letter

variable {A : Type*} [CommRing A] {p n k : ℕ} (D : DigitData A p)

/-- The output digit vector `c = π (g(a) e + b(a))`. -/
def outDigit (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) : Fin n → ZMod p :=
  fun j => dig D ℓ.2 ((mat x *ᵥ castVec ℓ.1 + vec x) j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.outDigit

/-- The output letter `(c, a)`. -/
def letter (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) : Letter p n k :=
  (outDigit D x ℓ, ℓ.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.letter

/-- The vector `g e + b - c`, whose entries have zero digits. -/
def z (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    Fin n → MvPolynomial (Fin k) A :=
  mat x *ᵥ castVec ℓ.1 + vec x - castVec (outDigit D x ℓ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.z

/-- The translation part `(σ_a (g e + b) - c) / p` of the state. -/
noncomputable def stateVec (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    Fin n → MvPolynomial (Fin k) A :=
  fun j => divP p (sigmaZ p ℓ.2 (z D x ℓ j))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.stateVec

/-- The state `(σ_a g, (σ_a (g e + b) - c) / p)`. -/
noncomputable def stateG (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    Aff n (MvPolynomial (Fin k) A) :=
  mk (stateVec D x ℓ) (Matrix.GeneralLinearGroup.map (sigmaZ p ℓ.2) x.right)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.stateG

variable [NeZero p]

theorem dig_z (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) (j : Fin n) :
    dig D ℓ.2 (z D x ℓ j) = 0 := by
  show dig D ℓ.2 ((mat x *ᵥ castVec ℓ.1 + vec x) j - castVec (outDigit D x ℓ) j) = 0
  rw [map_sub, dig_castVec]
  exact sub_self _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.dig_z

theorem sigmaZ_z (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) (j : Fin n) :
    sigmaZ p ℓ.2 (z D x ℓ j) = (p : MvPolynomial (Fin k) A) * stateVec D x ℓ j :=
  eq_mul_divP p (exists_sigmaZ_eq_mul D ℓ.2 (dig_z D x ℓ j))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigmaZ_z

theorem dig_mulVec_z (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) A))
    (y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) (j : Fin n) :
    dig D ℓ.2 ((M *ᵥ z D y ℓ) j) = 0 := by
  have h0 : ⇑(dig D ℓ.2) ∘ z D y ℓ = 0 := funext (dig_z D y ℓ)
  rw [RingHom.map_mulVec, h0, Matrix.mulVec_zero, Pi.zero_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.dig_mulVec_z

theorem outDigit_mul (x y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    outDigit D (x * y) ℓ = outDigit D x (letter D y ℓ) := by
  funext j
  have hc : castVec (outDigit D y ℓ) = mat y *ᵥ castVec ℓ.1 + vec y - z D y ℓ := by
    rw [z, sub_sub_cancel]
  have key : mat x *ᵥ castVec (outDigit D y ℓ) + vec x =
      (mat (x * y) *ᵥ castVec ℓ.1 + vec (x * y)) - mat x *ᵥ z D y ℓ := by
    rw [hc, mat_mul, vec_mul, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  show dig D ℓ.2 ((mat (x * y) *ᵥ castVec ℓ.1 + vec (x * y)) j) =
    dig D ℓ.2 ((mat x *ᵥ castVec (outDigit D y ℓ) + vec x) j)
  rw [key, Pi.sub_apply, map_sub, dig_mulVec_z, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.outDigit_mul

theorem z_mul (x y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    z D (x * y) ℓ = z D x (letter D y ℓ) + mat x *ᵥ z D y ℓ := by
  have h1 : z D (x * y) ℓ =
      mat (x * y) *ᵥ castVec ℓ.1 + vec (x * y) - castVec (outDigit D (x * y) ℓ) := rfl
  have h2 : z D x (letter D y ℓ) =
      mat x *ᵥ castVec (outDigit D y ℓ) + vec x - castVec (outDigit D x (letter D y ℓ)) := rfl
  have h3 : z D y ℓ = mat y *ᵥ castVec ℓ.1 + vec y - castVec (outDigit D y ℓ) := rfl
  rw [h1, h2, h3, outDigit_mul, mat_mul, vec_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_add]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.z_mul

variable [IsDomain A] [CharZero A]

theorem stateVec_mul (x y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    stateVec D (x * y) ℓ =
      stateVec D x (letter D y ℓ) + (mat x).map (sigmaZ p ℓ.2) *ᵥ stateVec D y ℓ := by
  funext j
  have hp : (p : MvPolynomial (Fin k) A) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  apply mul_left_cancel₀ hp
  have hy : ⇑(sigmaZ p ℓ.2) ∘ z D y ℓ = (p : MvPolynomial (Fin k) A) • stateVec D y ℓ :=
    funext fun i => sigmaZ_z D y ℓ i
  have hx : sigmaZ p ℓ.2 (z D x (letter D y ℓ) j) =
      (p : MvPolynomial (Fin k) A) * stateVec D x (letter D y ℓ) j :=
    sigmaZ_z D x (letter D y ℓ) j
  rw [← sigmaZ_z D (x * y) ℓ j, z_mul]
  simp only [Pi.add_apply, map_add, mul_add]
  rw [hx, RingHom.map_mulVec, hy, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.stateVec_mul

/-- **Cocycle rule**: `stateG (x y) ℓ = stateG x (letter y ℓ) * stateG y ℓ`. -/
theorem stateG_mul (x y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    stateG D (x * y) ℓ = stateG D x (letter D y ℓ) * stateG D y ℓ := by
  refine SemidirectProduct.ext ?_ ?_
  · show Multiplicative.ofAdd (stateVec D (x * y) ℓ) = Multiplicative.ofAdd
      (stateVec D x (letter D y ℓ) + (mat x).map (sigmaZ p ℓ.2) *ᵥ stateVec D y ℓ)
    rw [stateVec_mul]
  · exact map_mul (Matrix.GeneralLinearGroup.map (sigmaZ p ℓ.2)) x.right y.right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.stateG_mul

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
