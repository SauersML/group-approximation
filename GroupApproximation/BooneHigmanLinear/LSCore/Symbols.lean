import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Conjugation
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg and Dennis–Stein symbols over a commutative ring (k2-poly H.L4)

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25
(2020), arXiv:1909.02637, §2.2, in type `A_I` for the root `α = (i, j)`. Lane k2-hl4c. `w` and
`h` are `SteinbergWeyl`'s, `h_α(u) = w_α(u) w_α(-1)`.
* `ssym i j hij u v`: the Steinberg symbol `{u, v}_α = h_α(uv) h_α(u)⁻¹ h_α(v)⁻¹`, L–S (2.13).
* `dsym i j hij a b u`: the Dennis–Stein symbol
  `⟨a, b⟩_α = x_{-α}(-b/u) x_α(a) x_{-α}(b) x_α(-a/u) h_α(u)⁻¹`, L–S (2.14), written with the unit
  `u`. The lemmas that need it assume `(u : R) = 1 + a b`.
* `x_mul_x_dsym`: (2.14) solved for `x_α(a) x_{-α}(b)`. It holds for every unit `u`.
* (2.10) for `h_γ(t)` with `γ = (j, l)`, so `⟨α, γ⟩ = -1`: `h_conj_x_col` (`x_α(a) ↦ x_α(a t⁻¹)`)
  and `h_conj_x_row` (`x_{-α}(b) ↦ x_{-α}(t b)`). Then `h_conj_w` and (2.11) `h_conj_h`.
* `SymbolFacts`: centrality of the two symbols (they lie in `K₂`) and bimultiplicativity of
  `{-, -}`, L–S (2.16). These are standard. Route to discharge them for `|I| ≥ 4`: the symbols map to
  `1` in `E_I(R)`, `K₂` is central (k2-vdk's `VdKCentral` with `theorem1`), and bimultiplicativity
  then follows from the commutator identities, as in `Metabelian/ElemFPFieldK2Bimul` over a field.
* `dsym_scale`: `⟨a t⁻¹, m t⟩_α = ⟨a, m⟩_α {t⁻¹, 1 + am}_α`, which is L–S (5.12) with the
  conjugation by `h_γ(X)`, and its corollary `dsym_scale_mul` used for L–S Lemma 5.28.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j x_congr)

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- **L–S (2.13)**: `{u, v}_α = h_α(uv) h_α(u)⁻¹ h_α(v)⁻¹`. -/
def ssym (i j : I) (hij : i ≠ j) (u v : Rˣ) : SteinbergGroup I R :=
  h i j hij (u * v) * (h i j hij u)⁻¹ * (h i j hij v)⁻¹

/-- **L–S (2.14)**: `⟨a, b⟩_α = x_{-α}(-b u⁻¹) x_α(a) x_{-α}(b) x_α(-a u⁻¹) h_α(u)⁻¹`, for
`u = 1 + ab`. -/
def dsym (i j : I) (hij : i ≠ j) (a b : R) (u : Rˣ) : SteinbergGroup I R :=
  x j i hij.symm (-(b * ((u⁻¹ : Rˣ) : R))) * x i j hij a * x j i hij.symm b *
    x i j hij (-(a * ((u⁻¹ : Rˣ) : R))) * (h i j hij u)⁻¹

theorem h_def (i j : I) (hij : i ≠ j) (u : Rˣ) :
    h i j hij u = w i j hij u * w (R := R) i j hij (-1) :=
  rfl

theorem h_one (i j : I) (hij : i ≠ j) : h (R := R) i j hij 1 = 1 := by
  rw [h_def, ← w_inv, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_one

theorem ssym_one_left (i j : I) (hij : i ≠ j) (v : Rˣ) : ssym (R := R) i j hij 1 v = 1 := by
  unfold ssym
  rw [one_mul, h_one]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.ssym_one_left

/-- (2.13) rearranged: `h_α(sv) h_α(s)⁻¹ = {s, v}_α h_α(v)`. -/
theorem h_mul_inv_h (i j : I) (hij : i ≠ j) (s v : Rˣ) :
    h (R := R) i j hij (s * v) * (h i j hij s)⁻¹ = ssym i j hij s v * h i j hij v := by
  unfold ssym
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_mul_inv_h

/-- **L–S (2.14)** solved for `x_α(a) x_{-α}(b)`; true for every unit `u`. -/
theorem x_mul_x_dsym (i j : I) (hij : i ≠ j) (a b : R) (u : Rˣ) :
    x i j hij a * x j i hij.symm b =
      x j i hij.symm (b * ((u⁻¹ : Rˣ) : R)) * dsym i j hij a b u * h i j hij u *
        x i j hij (a * ((u⁻¹ : Rˣ) : R)) := by
  unfold dsym
  simp only [x_neg]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.x_mul_x_dsym

/-- Conjugation by `h_ij(u)` is conjugation by `w_ij(-1)` followed by `w_ij(u)`. -/
theorem h_conj_split_w (i j : I) (hij : i ≠ j) (u : Rˣ) (g : SteinbergGroup I R) :
    h i j hij u * g * (h i j hij u)⁻¹ =
      w i j hij u * (w i j hij (-1) * g * (w i j hij (-1))⁻¹) * (w i j hij u)⁻¹ := by
  simp only [h, mul_inv_rev, mul_assoc]

/-- **L–S (2.10)**, `γ = (j, l)`, `⟨α, γ⟩ = -1`: `h_γ(t) x_α(a) h_γ(t)⁻¹ = x_α(a t⁻¹)`. -/
theorem h_conj_x_col (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (t : Rˣ) (a : R) :
    h j l hjl t * x i j hij a * (h j l hjl t)⁻¹ = x i j hij (a * ((t⁻¹ : Rˣ) : R)) := by
  rw [h_conj_split_w, w_conj_x_col_i j l i hjl hij hil, w_conj_x_col_j j l i hjl hij hil]
  exact x_congr _ _ rfl rfl (by simp)

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_conj_x_col

/-- **L–S (2.10)**, `γ = (j, l)`: `h_γ(t) x_{-α}(b) h_γ(t)⁻¹ = x_{-α}(t b)`. -/
theorem h_conj_x_row (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (t : Rˣ) (b : R) :
    h j l hjl t * x j i hij.symm b * (h j l hjl t)⁻¹ = x j i hij.symm ((t : R) * b) := by
  rw [h_conj_split_w, w_conj_x_row_i j l i hjl hij.symm hil.symm,
    w_conj_x_row_j j l i hjl hij.symm hil.symm]
  exact x_congr _ _ rfl rfl (by simp)

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_conj_x_row

/-- `h_γ(t) w_α(v) h_γ(t)⁻¹ = w_α(v t⁻¹)` for `γ = (j, l)`. -/
theorem h_conj_w (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (t v : Rˣ) :
    h j l hjl t * w i j hij v * (h j l hjl t)⁻¹ = w (R := R) i j hij (v * t⁻¹) := by
  have e : ∀ A B C : SteinbergGroup I R, h j l hjl t * (A * B * C) * (h j l hjl t)⁻¹ =
      (h j l hjl t * A * (h j l hjl t)⁻¹) * (h j l hjl t * B * (h j l hjl t)⁻¹) *
        (h j l hjl t * C * (h j l hjl t)⁻¹) := fun A B C => by group
  simp only [w]
  rw [e, h_conj_x_col i j l hij hjl hil, h_conj_x_row i j l hij hjl hil]
  simp only [Units.val_mul, mul_inv_rev, inv_inv, mul_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_conj_w

/-- **L–S (2.11)**, `γ = (j, l)`: `h_γ(t) h_α(u) h_γ(t)⁻¹ = h_α(u t⁻¹) h_α(t⁻¹)⁻¹`. -/
theorem h_conj_h (i j l : I) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (t u : Rˣ) :
    h j l hjl t * h i j hij u * (h j l hjl t)⁻¹ =
      h (R := R) i j hij (u * t⁻¹) * (h i j hij t⁻¹)⁻¹ := by
  have e : ∀ A B : SteinbergGroup I R, h j l hjl t * (A * B) * (h j l hjl t)⁻¹ =
      (h j l hjl t * A * (h j l hjl t)⁻¹) * (h j l hjl t * B * (h j l hjl t)⁻¹) :=
    fun A B => by group
  rw [h_def i j hij u, e, h_conj_w i j l hij hjl hil, h_conj_w i j l hij hjl hil,
    h_def i j hij (u * t⁻¹), h_def i j hij t⁻¹, neg_one_mul, ← w_inv i j hij t⁻¹]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.h_conj_h

variable (R) in
/-- The standard symbol facts used in L–S §5.3, for one root `α = (i, j)`: both symbols are
central (they lie in `K₂`), and `{-, -}_α` is bimultiplicative (L–S (2.16)). -/
structure SymbolFacts (i j : I) (hij : i ≠ j) : Prop where
  ssym_central : ∀ (u v : Rˣ) (g : SteinbergGroup I R), Commute (ssym i j hij u v) g
  dsym_central : ∀ (a b : R) (u : Rˣ), (u : R) = 1 + a * b →
    ∀ g : SteinbergGroup I R, Commute (dsym i j hij a b u) g
  ssym_mul_left : ∀ u₁ u₂ v : Rˣ,
    ssym i j hij (u₁ * u₂) v = ssym i j hij u₁ v * ssym (R := R) i j hij u₂ v
  ssym_mul_right : ∀ u v₁ v₂ : Rˣ,
    ssym i j hij u (v₁ * v₂) = ssym i j hij u v₁ * ssym (R := R) i j hij u v₂

/-- **L–S (5.12)**, rearranged: `⟨a t⁻¹, m t⟩_α = ⟨a, m⟩_α {t⁻¹, u}_α` for `u = 1 + am`. The proof
conjugates by `h_γ(t)`, `γ = (j, l)`, as L–S do with `t = X`. -/
theorem dsym_scale {i j l : I} {hij : i ≠ j} (hF : SymbolFacts R i j hij) (hjl : j ≠ l)
    (hil : i ≠ l) (t u : Rˣ) (a m : R) (hu : (u : R) = 1 + a * m) :
    dsym i j hij (a * ((t⁻¹ : Rˣ) : R)) (m * (t : R)) u =
      dsym i j hij a m u * ssym i j hij t⁻¹ u := by
  have e1 : x j i hij.symm (-(m * (t : R) * ((u⁻¹ : Rˣ) : R))) =
      h j l hjl t * x j i hij.symm (-(m * ((u⁻¹ : Rˣ) : R))) * (h j l hjl t)⁻¹ := by
    rw [h_conj_x_row i j l hij hjl hil]
    exact x_congr _ _ rfl rfl (by ring)
  have e2 : x i j hij (a * ((t⁻¹ : Rˣ) : R)) = h j l hjl t * x i j hij a * (h j l hjl t)⁻¹ :=
    (h_conj_x_col i j l hij hjl hil t a).symm
  have e3 : x j i hij.symm (m * (t : R)) = h j l hjl t * x j i hij.symm m * (h j l hjl t)⁻¹ := by
    rw [h_conj_x_row i j l hij hjl hil]
    exact x_congr _ _ rfl rfl (by ring)
  have e4 : x i j hij (-(a * ((t⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R))) =
      h j l hjl t * x i j hij (-(a * ((u⁻¹ : Rˣ) : R))) * (h j l hjl t)⁻¹ := by
    rw [h_conj_x_col i j l hij hjl hil]
    exact x_congr _ _ rfl rfl (by ring)
  have hD : h j l hjl t * dsym i j hij a m u * (h j l hjl t)⁻¹ = dsym i j hij a m u := by
    rw [(hF.dsym_central a m u hu (h j l hjl t)).symm.eq, mul_inv_cancel_right]
  calc dsym i j hij (a * ((t⁻¹ : Rˣ) : R)) (m * (t : R)) u
      = x j i hij.symm (-(m * (t : R) * ((u⁻¹ : Rˣ) : R))) * x i j hij (a * ((t⁻¹ : Rˣ) : R)) *
          x j i hij.symm (m * (t : R)) * x i j hij (-(a * ((t⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R))) *
          (h i j hij u)⁻¹ := rfl
    _ = h j l hjl t * (dsym i j hij a m u * h i j hij u) * (h j l hjl t)⁻¹ *
          (h i j hij u)⁻¹ := by
        rw [e1, e2, e3, e4]
        unfold dsym
        group
    _ = (h j l hjl t * dsym i j hij a m u * (h j l hjl t)⁻¹) *
          (h j l hjl t * h i j hij u * (h j l hjl t)⁻¹) * (h i j hij u)⁻¹ := by
        group
    _ = dsym i j hij a m u * (h i j hij (u * t⁻¹) * (h i j hij t⁻¹)⁻¹) * (h i j hij u)⁻¹ := by
        rw [hD, h_conj_h i j l hij hjl hil t u]
    _ = dsym i j hij a m u * ssym i j hij t⁻¹ u := by
        rw [mul_comm u t⁻¹, h_mul_inv_h]
        group

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.dsym_scale

/-- `⟨a t⁻¹, m t⟩_α {t, u}_α = ⟨a, m⟩_α` for `u = 1 + am`. -/
theorem dsym_scale_mul {i j l : I} {hij : i ≠ j} (hF : SymbolFacts R i j hij) (hjl : j ≠ l)
    (hil : i ≠ l) (t u : Rˣ) (a m : R) (hu : (u : R) = 1 + a * m) :
    dsym i j hij (a * ((t⁻¹ : Rˣ) : R)) (m * (t : R)) u * ssym i j hij t u =
      dsym i j hij a m u := by
  rw [dsym_scale hF hjl hil t u a m hu, mul_assoc, ← hF.ssym_mul_left, inv_mul_cancel,
    ssym_one_left, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.LSCore.dsym_scale_mul

end LSCore
end BooneHigmanLinear
end GroupApproximation
