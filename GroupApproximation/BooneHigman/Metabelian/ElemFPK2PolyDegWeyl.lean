import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2WeylSelf
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Unified
import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree reduction for `K₂(F_p[X])`, part 1: ring-generic Weyl and torus conjugation

Lane `bh-met-91c`.  Over any ring `R`, with `i ≠ j`, a unit `u` and a third index `n ∉ {i, j}`:

* `k2PolyDeg_ringMap_w`, `k2PolyDeg_ringMap_h`: a ring map sends `w_ij(u)`, `h_ij(u)` to
  `w_ij(f u)`, `h_ij(f u)`.
* `k2PolyDeg_w_conj_self`, `k2PolyDeg_w_conj_self_symm`: `w_ij(u)` sends `x_ij(t)` into the
  root group of `(j, i)` and `x_ji(t)` into that of `(i, j)`.  These are the ring versions of
  `FieldK2.w_conj_x_self(_symm)`; only the coefficient is left existential.
* `k2PolyDeg_w_conj_self_symm_eq` (commutative `R`): `w_ij(u) x_ji(t) w_ij(u)⁻¹ = x_ij(-(utu))`.
* `k2PolyDeg_w_conj_exists`: `w_ij(u) x_kl(a) w_ij(u)⁻¹ = x_{τk τl}(b)`, `τ = swap i j`, for
  every root `(k, l)`.
* `k2PolyDeg_h_conj_exists`: `h_ij(u) x_kl(a) h_ij(u)⁻¹ = x_kl(b)` for every root `(k, l)`.

Truth check (paper).  `x_ij(t) = ⁅x_in(t), x_nj(1)⁆`, and `w` sends `x_in` to the root `(j, n)`
and `x_nj` to the root `(n, i)`, whose commutator lies in the root `(j, i)`.  Since
`h = w(u) w(-1)` and `τ ∘ τ = id`, `h` preserves every root group.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j w_conj_x x_congr)

variable {I : Type*} [Fintype I] [DecidableEq I]

section RingMap

variable {A B : Type*} [Ring A] [Ring B]

/-- A ring map sends `w_ij(u)` to `w_ij(f u)`. -/
theorem k2PolyDeg_ringMap_w (f : A →+* B) (i j : I) (hij : i ≠ j) (u : Aˣ) :
    ringMap f (w i j hij u) = w i j hij (Units.map f.toMonoidHom u) := by
  have e1 : ((Units.map f.toMonoidHom u : Bˣ) : B) = f (u : A) := rfl
  have e2 : (((Units.map f.toMonoidHom u)⁻¹ : Bˣ) : B) = f ((u⁻¹ : Aˣ) : A) := rfl
  simp only [w, map_mul, ringMap_x, e1, e2, map_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ringMap_w

/-- A ring map sends `h_ij(u)` to `h_ij(f u)`. -/
theorem k2PolyDeg_ringMap_h (f : A →+* B) (i j : I) (hij : i ≠ j) (u : Aˣ) :
    ringMap f (h i j hij u) = h i j hij (Units.map f.toMonoidHom u) := by
  have e : Units.map f.toMonoidHom (-1 : Aˣ) = -1 :=
    Units.ext (show f (-(1 : A)) = -(1 : B) by rw [map_neg, map_one])
  rw [h, h, map_mul, k2PolyDeg_ringMap_w, k2PolyDeg_ringMap_w, e]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ringMap_h

end RingMap

section Self

variable {R : Type*} [Ring R]

/-- `w_ij(u) x_ij(t) w_ij(u)⁻¹` lies in the root group of `(j, i)` (any ring). -/
theorem k2PolyDeg_w_conj_self (i j n : I) (hij : i ≠ j) (hin : i ≠ n) (hjn : j ≠ n)
    (u : Rˣ) (t : R) :
    ∃ b : R, w i j hij u * x i j hij t * (w i j hij u)⁻¹ = x j i hij.symm b := by
  have e : x i j hij t = ⁅x i n hin t, x n j hjn.symm 1⁆ := by
    rw [x_commutator i n j hin hjn.symm hij t 1, mul_one]
  rw [e, FieldK2.conj_commutator', w_conj_x_row_i i j n hij hin hjn u t,
    w_conj_x_col_j i j n hij hin.symm hjn.symm u 1, x_commutator j n i hjn hin.symm hij.symm]
  exact ⟨_, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_w_conj_self

/-- `w_ij(u) x_ji(t) w_ij(u)⁻¹` lies in the root group of `(i, j)` (any ring). -/
theorem k2PolyDeg_w_conj_self_symm (i j n : I) (hij : i ≠ j) (hin : i ≠ n) (hjn : j ≠ n)
    (u : Rˣ) (t : R) :
    ∃ b : R, w i j hij u * x j i hij.symm t * (w i j hij u)⁻¹ = x i j hij b := by
  have e : x j i hij.symm t = ⁅x j n hjn t, x n i hin.symm 1⁆ := by
    rw [x_commutator j n i hjn hin.symm hij.symm t 1, mul_one]
  rw [e, FieldK2.conj_commutator', w_conj_x_row_j i j n hij hin hjn u t,
    w_conj_x_col_i i j n hij hin.symm hjn.symm u 1, x_commutator i n j hin hjn.symm hij]
  exact ⟨_, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_w_conj_self_symm

end Self

/-- Over a commutative ring, `w_ij(u) x_ji(t) w_ij(u)⁻¹ = x_ij(-(u t u))`. -/
theorem k2PolyDeg_w_conj_self_symm_eq {R : Type*} [CommRing R] (i j n : I) (hij : i ≠ j)
    (hin : i ≠ n) (hjn : j ≠ n) (u : Rˣ) (t : R) :
    w i j hij u * x j i hij.symm t * (w i j hij u)⁻¹ =
      x i j hij (-((u : R) * t * (u : R))) := by
  have e : x j i hij.symm t = ⁅x j n hjn t, x n i hin.symm 1⁆ := by
    rw [x_commutator j n i hjn hin.symm hij.symm t 1, mul_one]
  rw [e, FieldK2.conj_commutator', w_conj_x_row_j i j n hij hin hjn u t,
    w_conj_x_col_i i j n hij hin.symm hjn.symm u 1, x_commutator i n j hin hjn.symm hij]
  exact x_congr _ _ rfl rfl (by ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_w_conj_self_symm_eq

section Conj

variable {R : Type*} [Ring R]

/-- `w_ij(u)` sends the root group of `(k, l)` into that of `(τ k, τ l)`, `τ = swap i j`. -/
theorem k2PolyDeg_w_conj_exists (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hthird : ∃ n, i ≠ n ∧ j ≠ n) (u : Rˣ) (a : R) :
    ∃ b : R, w i j hij u * x k l hkl a * (w i j hij u)⁻¹ =
      x (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) b := by
  obtain ⟨n, hin, hjn⟩ := hthird
  by_cases h1 : k = i ∧ l = j
  · have e : x k l hkl a = x i j hij a := x_congr _ _ h1.1 h1.2 rfl
    rw [e]
    obtain ⟨b, hb⟩ := k2PolyDeg_w_conj_self i j n hij hin hjn u a
    refine ⟨b, hb.trans (x_congr _ _ ?_ ?_ rfl)⟩
    · rw [h1.1, Equiv.swap_apply_left]
    · rw [h1.2, Equiv.swap_apply_right]
  by_cases h2 : k = j ∧ l = i
  · have e : x k l hkl a = x j i hij.symm a := x_congr _ _ h2.1 h2.2 rfl
    rw [e]
    obtain ⟨b, hb⟩ := k2PolyDeg_w_conj_self_symm i j n hij hin hjn u a
    refine ⟨b, hb.trans (x_congr _ _ ?_ ?_ rfl)⟩
    · rw [h2.1, Equiv.swap_apply_right]
    · rw [h2.2, Equiv.swap_apply_left]
  exact ⟨_, w_conj_x i j k l hij hkl h1 h2 u a⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_w_conj_exists

/-- `h_ij(u)` preserves every root group. -/
theorem k2PolyDeg_h_conj_exists (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hthird : ∃ n, i ≠ n ∧ j ≠ n) (u : Rˣ) (a : R) :
    ∃ b : R, h i j hij u * x k l hkl a * (h i j hij u)⁻¹ = x k l hkl b := by
  obtain ⟨b₁, hb₁⟩ := k2PolyDeg_w_conj_exists i j k l hij hkl hthird (-1) a
  obtain ⟨b₂, hb₂⟩ := k2PolyDeg_w_conj_exists i j _ _ hij
    ((Equiv.swap i j).injective.ne hkl) hthird u b₁
  refine ⟨b₂, ?_⟩
  have e : h i j hij u * x k l hkl a * (h i j hij u)⁻¹ =
      w i j hij u * (w i j hij (-1) * x k l hkl a * (w i j hij (-1))⁻¹) *
        (w i j hij u)⁻¹ := by
    rw [h]
    group
  rw [e, hb₁, hb₂]
  exact x_congr _ _ (Equiv.swap_apply_self i j k) (Equiv.swap_apply_self i j l) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_h_conj_exists

end Conj

end GroupApproximation.BooneHigman.Metabelian.ElemFP
