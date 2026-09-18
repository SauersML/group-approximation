import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2HConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over a field are central

Lane `bh-met-15`.  Over a field `R`, with `i ≠ j` and units `u, v`, the symbol is
`symbol i j hij u v = h_ij(uv) h_ij(u)⁻¹ h_ij(v)⁻¹`.  If `I` has a third index `k ∉ {i, j}`,
the symbol commutes with every element of `St_I(R)` (`symbol_commute`).

Truth check.  By `ElemFPFieldK2HConj`, conjugation by `h_ij(u)` multiplies the coefficient of
`x_pq` by a scalar `λ_pq(u)`, and `λ_pq(uv) = λ_pq(u) λ_pq(v)`.  So conjugation by the symbol
multiplies it by `λ(uv) λ(u)⁻¹ λ(v)⁻¹ = 1`.  This is the abstract `conj_symbol_eq`.  The root
elements generate the presented group (`PresentedGroup.generated_by`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h x_congr)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- The Steinberg symbol `h_ij(uv) h_ij(u)⁻¹ h_ij(v)⁻¹`. -/
def symbol (i j : I) (hij : i ≠ j) (u v : Rˣ) : SteinbergGroup I R :=
  h i j hij (u * v) * (h i j hij u)⁻¹ * (h i j hij v)⁻¹

/-- If `A, B, C` scale the coefficient of a root map `X` by `α = βγ`, `β` and `γ`, then
`A B⁻¹ C⁻¹` fixes every `X t`. -/
theorem conj_symbol_eq {G : Type*} [Group G] (X : R → G) {A B C : G} {α β γ : R}
    (hA : ∀ t, A * X t * A⁻¹ = X (α * t)) (hB : ∀ t, B * X t * B⁻¹ = X (β * t))
    (hC : ∀ t, C * X t * C⁻¹ = X (γ * t)) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hαβγ : α = β * γ)
    (t : R) : A * B⁻¹ * C⁻¹ * X t * (A * B⁻¹ * C⁻¹)⁻¹ = X t := by
  have hinv : ∀ {D : G} {δ : R}, (∀ s, D * X s * D⁻¹ = X (δ * s)) → δ ≠ 0 →
      ∀ s, D⁻¹ * X s * D = X (δ⁻¹ * s) := by
    intro D δ hD hδ s
    calc D⁻¹ * X s * D = D⁻¹ * (D * X (δ⁻¹ * s) * D⁻¹) * D := by
          rw [hD, mul_inv_cancel_left₀ hδ]
      _ = X (δ⁻¹ * s) := by group
  calc A * B⁻¹ * C⁻¹ * X t * (A * B⁻¹ * C⁻¹)⁻¹ =
        A * (B⁻¹ * (C⁻¹ * X t * C) * B) * A⁻¹ := by group
    _ = X t := by
      rw [hinv hC hγ, hinv hB hβ, hA, hαβγ, mul_comm β γ, mul_assoc,
        mul_inv_cancel_left₀ hβ, mul_inv_cancel_left₀ hγ]

variable (i j : I) (hij : i ≠ j) (u v : Rˣ)

theorem symbol_conj_ij (k : I) (hik : i ≠ k) (hjk : j ≠ k) (t : R) :
    symbol i j hij u v * x i j hij t * (symbol i j hij u v)⁻¹ = x i j hij t := by
  unfold symbol
  exact conj_symbol_eq (x i j hij) (h_conj_ij i j k hij hik hjk (u * v))
    (h_conj_ij i j k hij hik hjk u) (h_conj_ij i j k hij hik hjk v)
    (mul_ne_zero u.ne_zero u.ne_zero) (mul_ne_zero v.ne_zero v.ne_zero)
    (by rw [Units.val_mul]; ring) t

theorem symbol_conj_ji (k : I) (hik : i ≠ k) (hjk : j ≠ k) (t : R) :
    symbol i j hij u v * x j i hij.symm t * (symbol i j hij u v)⁻¹ = x j i hij.symm t := by
  unfold symbol
  exact conj_symbol_eq (x j i hij.symm) (h_conj_ji i j k hij hik hjk (u * v))
    (h_conj_ji i j k hij hik hjk u) (h_conj_ji i j k hij hik hjk v)
    (mul_ne_zero (inv_ne_zero u.ne_zero) (inv_ne_zero u.ne_zero))
    (mul_ne_zero (inv_ne_zero v.ne_zero) (inv_ne_zero v.ne_zero))
    (by rw [Units.val_mul, mul_inv]; ring) t

theorem symbol_conj_iq (q : I) (hiq : i ≠ q) (hjq : j ≠ q) (t : R) :
    symbol i j hij u v * x i q hiq t * (symbol i j hij u v)⁻¹ = x i q hiq t := by
  unfold symbol
  exact conj_symbol_eq (x i q hiq) (h_conj_iq i j q hij hiq hjq (u * v))
    (h_conj_iq i j q hij hiq hjq u) (h_conj_iq i j q hij hiq hjq v)
    u.ne_zero v.ne_zero (Units.val_mul u v) t

theorem symbol_conj_jq (q : I) (hiq : i ≠ q) (hjq : j ≠ q) (t : R) :
    symbol i j hij u v * x j q hjq t * (symbol i j hij u v)⁻¹ = x j q hjq t := by
  unfold symbol
  exact conj_symbol_eq (x j q hjq) (h_conj_jq i j q hij hiq hjq (u * v))
    (h_conj_jq i j q hij hiq hjq u) (h_conj_jq i j q hij hiq hjq v)
    (inv_ne_zero u.ne_zero) (inv_ne_zero v.ne_zero) (by rw [Units.val_mul, mul_inv]) t

theorem symbol_conj_pi (p : I) (hpi : p ≠ i) (hpj : p ≠ j) (t : R) :
    symbol i j hij u v * x p i hpi t * (symbol i j hij u v)⁻¹ = x p i hpi t := by
  unfold symbol
  exact conj_symbol_eq (x p i hpi) (h_conj_pi i j p hij hpi hpj (u * v))
    (h_conj_pi i j p hij hpi hpj u) (h_conj_pi i j p hij hpi hpj v)
    (inv_ne_zero u.ne_zero) (inv_ne_zero v.ne_zero) (by rw [Units.val_mul, mul_inv]) t

theorem symbol_conj_pj (p : I) (hpi : p ≠ i) (hpj : p ≠ j) (t : R) :
    symbol i j hij u v * x p j hpj t * (symbol i j hij u v)⁻¹ = x p j hpj t := by
  unfold symbol
  exact conj_symbol_eq (x p j hpj) (h_conj_pj i j p hij hpi hpj (u * v))
    (h_conj_pj i j p hij hpi hpj u) (h_conj_pj i j p hij hpi hpj v)
    u.ne_zero v.ne_zero (Units.val_mul u v) t

theorem symbol_conj_pq (p q : I) (hpq : p ≠ q) (hip : i ≠ p) (hjp : j ≠ p) (hiq : i ≠ q)
    (hjq : j ≠ q) (t : R) :
    symbol i j hij u v * x p q hpq t * (symbol i j hij u v)⁻¹ = x p q hpq t := by
  unfold symbol
  exact conj_symbol_eq (x p q hpq) (h_conj_pq i j p q hij hpq hip hjp hiq hjq (u * v))
    (h_conj_pq i j p q hij hpq hip hjp hiq hjq u) (h_conj_pq i j p q hij hpq hip hjp hiq hjq v)
    one_ne_zero one_ne_zero (mul_one 1).symm t

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_symbol_eq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_ij
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_ji
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_iq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_jq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_pi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_pj
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_pq
