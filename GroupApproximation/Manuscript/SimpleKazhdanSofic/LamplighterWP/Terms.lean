import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblemPrimrec
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Multiplying out words in `G_Δ`: polynomial terms

`simple_kazhdan_sofic_group.tex`, section "LEF groups", proof of `cor:lef`, second statement,
l.448–455:

> A word in the generators of $G_\Delta$ multiplies out to a matrix with entries
> $\sum_\xi p_\xi u_\xi$, where each $p_\xi$ is a polynomial over $\F_2$ in finitely many coordinates
> $x(\delta)$, as $u_\xi e_Uu_\xi^{-1}$ is the indicator of $\{x:x(\delta)=1+c(\delta)\}$ for
> $\xi\colon x\mapsto\delta x+c$.

## Proof route

Everything is written with words `w` in the generators `lampGen t` of `Λ` (letters `Option ι × Bool`).

* A *factor* `fac t w` is the function `x ↦ (ξ⁻¹ x)(e)`, `ξ` the value of `w`, i.e. `u_ξ e_U u_ξ⁻¹`
  evaluated as a function. By `smul_apply` it is `x ↦ x(δ) + c`, with `δ = ξ.right` and a constant
  `c = fac t w 0` (`fac_eq`).
* A *term* `(L, v)` is `(∏_{w ∈ L} fac t w) u_{value v}` (`termEval`), a *polynomial* is a list of
  terms (`polyEval`), and a matrix of polynomials is evaluated entrywise (`matEval`).
* Terms multiply by `(L, v)(M, v') = (L ++ v·M, v v')` (`termEval_termMul`), from
  `u_ξ f = (f ∘ ξ⁻¹) u_ξ` and `comap_fac`; so polynomials and matrices multiply
  (`polyEval_polyMul`, `matEval_matMul`).
* `R_Δ` has characteristic `2` (`add_self_lampRing`), so `1 - s E_ij = 1 + s E_ij`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LamplighterWP

open GroupApproximation.SimpleKazhdanSofic.Lamplighter
open SkewMonoidAlgebra (single)

/-- Words in the generators `lampGen t` of `Λ`. -/
abbrev LW (ι : Type) : Type := List (Option ι × Bool)

/-- A term: a list of factor words and a unit word. -/
abbrev LTerm (ι : Type) : Type := List (LW ι) × LW ι

/-- A polynomial: a list of terms. -/
abbrev LPoly (ι : Type) : Type := List (LTerm ι)

/-- A `3 × 3` matrix of polynomials. -/
abbrev LMat (ι : Type) : Type := Fin 3 → Fin 3 → LPoly ι

variable {Δ : Type} [Group Δ] {ι : Type}

/-! ### Factors -/

/-- The factor of a word `w` with value `ξ`: `x ↦ (ξ⁻¹ x)(e)`, the function `u_ξ e_U u_ξ⁻¹`. -/
noncomputable def fac (t : ι → Δ) (w : LW ι) : LocallyConstant (LampSpace Δ) (ZMod 2) :=
  LocallyConstant.comap
    (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) w)⁻¹)
    (Lamplighter.coord Δ 1)

theorem fac_apply (t : ι → Δ) (w : LW ι) (x : LampSpace Δ) :
    fac t w x = ((wordValue (lampGen t) w)⁻¹ • x) 1 :=
  rfl

/-- **A factor is a coordinate plus a constant** (l.451): `fac t w x = x(δ) + c`. -/
theorem fac_eq (t : ι → Δ) (w : LW ι) (v : LampSpace Δ) :
    fac t w v = v (SemidirectProduct.right (wordValue (lampGen t) w)) + fac t w 0 := by
  rw [fac_apply, fac_apply, Lamplighter.smul_apply, Lamplighter.smul_apply, Pi.zero_apply, zero_add,
    SemidirectProduct.inv_right, inv_inv, mul_one]

/-- Translating a factor by the value of `v` gives the factor of `v ++ w`. -/
theorem comap_fac (t : ι → Δ) (v w : LW ι) :
    LocallyConstant.comap
      (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) v)⁻¹)
      (fac t w) = fac t (v ++ w) := by
  ext x
  show ((wordValue (lampGen t) w)⁻¹ • (wordValue (lampGen t) v)⁻¹ • x) 1 =
    ((wordValue (lampGen t) (v ++ w))⁻¹ • x) 1
  rw [wordValue_append, mul_inv_rev, mul_smul]

/-- The product of the factors of a list of words. -/
noncomputable def termFun (t : ι → Δ) : List (LW ι) → LocallyConstant (LampSpace Δ) (ZMod 2)
  | [] => 1
  | w :: L => fac t w * termFun t L

theorem termFun_nil (t : ι → Δ) : termFun t ([] : List (LW ι)) = 1 :=
  rfl

theorem termFun_cons (t : ι → Δ) (w : LW ι) (L : List (LW ι)) :
    termFun t (w :: L) = fac t w * termFun t L :=
  rfl

theorem termFun_append (t : ι → Δ) (L M : List (LW ι)) :
    termFun t (L ++ M) = termFun t L * termFun t M := by
  induction L with
  | nil => rw [List.nil_append, termFun_nil, one_mul]
  | cons w L ih => rw [List.cons_append, termFun_cons, termFun_cons, ih, mul_assoc]

theorem comap_termFun (t : ι → Δ) (v : LW ι) (L : List (LW ι)) :
    LocallyConstant.comap
      (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) v)⁻¹)
      (termFun t L) = termFun t (L.map (v ++ ·)) := by
  induction L with
  | nil => exact LocallyConstant.ext fun _ => rfl
  | cons w L ih =>
    rw [List.map_cons, termFun_cons, termFun_cons, ← comap_fac t v w, ← ih]
    exact LocallyConstant.ext fun _ => rfl

/-! ### Terms and polynomials -/

/-- The value `(∏_{w ∈ L} fac t w) u_{value v}` of a term `(L, v)`. -/
noncomputable def termEval (t : ι → Δ) (τ : LTerm ι) : LampRing Δ :=
  single (wordValue (lampGen t) τ.2)
    (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (termFun t τ.1))

/-- The product of two terms. -/
def termMul (τ σ : LTerm ι) : LTerm ι :=
  (τ.1 ++ σ.1.map (τ.2 ++ ·), τ.2 ++ σ.2)

theorem termMul_fst (τ σ : LTerm ι) : (termMul τ σ).1 = τ.1 ++ σ.1.map (τ.2 ++ ·) :=
  rfl

theorem termMul_snd (τ σ : LTerm ι) : (termMul τ σ).2 = τ.2 ++ σ.2 :=
  rfl

/-- **Terms multiply** by `f u_ξ · f' u_η = f (f' ∘ ξ⁻¹) u_{ξη}`. -/
theorem termEval_termMul (t : ι → Δ) (τ σ : LTerm ι) :
    termEval t (termMul τ σ) = termEval t τ * termEval t σ := by
  unfold termEval
  rw [termMul_fst, termMul_snd, wordValue_append, termFun_append,
    SkewMonoidAlgebra.single_mul_single, ClopenGroupCoeff.smul_of, comap_termFun,
    map_mul (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2))]

/-- The value of a polynomial: the sum of its terms. -/
noncomputable def polyEval (t : ι → Δ) : LPoly ι → LampRing Δ
  | [] => 0
  | τ :: P => termEval t τ + polyEval t P

theorem polyEval_nil (t : ι → Δ) : polyEval t ([] : LPoly ι) = 0 :=
  rfl

theorem polyEval_cons (t : ι → Δ) (τ : LTerm ι) (P : LPoly ι) :
    polyEval t (τ :: P) = termEval t τ + polyEval t P :=
  rfl

theorem polyEval_append (t : ι → Δ) (P Q : LPoly ι) :
    polyEval t (P ++ Q) = polyEval t P + polyEval t Q := by
  induction P with
  | nil => rw [List.nil_append, polyEval_nil, zero_add]
  | cons τ P ih => rw [List.cons_append, polyEval_cons, polyEval_cons, ih, add_assoc]

/-- The product of two polynomials. -/
def polyMul (P Q : LPoly ι) : LPoly ι :=
  P.flatMap fun τ => Q.map (termMul τ)

theorem polyMul_nil (Q : LPoly ι) : polyMul [] Q = [] :=
  rfl

theorem polyMul_cons (τ : LTerm ι) (P Q : LPoly ι) :
    polyMul (τ :: P) Q = Q.map (termMul τ) ++ polyMul P Q :=
  List.flatMap_cons

theorem polyEval_map_termMul (t : ι → Δ) (τ : LTerm ι) (Q : LPoly ι) :
    polyEval t (Q.map (termMul τ)) = termEval t τ * polyEval t Q := by
  induction Q with
  | nil => rw [List.map_nil, polyEval_nil, mul_zero]
  | cons σ Q ih => rw [List.map_cons, polyEval_cons, polyEval_cons, ih, termEval_termMul, mul_add]

/-- **Polynomials multiply.** -/
theorem polyEval_polyMul (t : ι → Δ) (P Q : LPoly ι) :
    polyEval t (polyMul P Q) = polyEval t P * polyEval t Q := by
  induction P with
  | nil => rw [polyMul_nil, polyEval_nil, zero_mul]
  | cons τ P ih => rw [polyMul_cons, polyEval_append, polyEval_map_termMul, ih, polyEval_cons, add_mul]

/-- The polynomial `1`. -/
theorem polyEval_unit (t : ι → Δ) : polyEval t ([([], [])] : LPoly ι) = 1 := by
  rw [polyEval_cons, polyEval_nil, add_zero]
  show single (wordValue (lampGen t) ([] : LW ι))
    (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (termFun t ([] : List (LW ι)))) = 1
  rw [wordValue_nil, termFun_nil, map_one (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)),
    SkewMonoidAlgebra.single_one_one]

/-! ### Matrices -/

/-- Entrywise evaluation of a matrix of polynomials. -/
noncomputable def matEval (t : ι → Δ) (M : LMat ι) : Matrix (Fin 3) (Fin 3) (LampRing Δ) :=
  Matrix.of fun p q => polyEval t (M p q)

theorem matEval_apply (t : ι → Δ) (M : LMat ι) (p q : Fin 3) :
    matEval t M p q = polyEval t (M p q) :=
  rfl

/-- The product of matrices of polynomials. -/
def matMul (M N : LMat ι) (p q : Fin 3) : LPoly ι :=
  polyMul (M p 0) (N 0 q) ++ polyMul (M p 1) (N 1 q) ++ polyMul (M p 2) (N 2 q)

theorem matEval_matMul (t : ι → Δ) (M N : LMat ι) :
    matEval t (matMul M N) = matEval t M * matEval t N := by
  ext p q
  simp only [matEval_apply, Matrix.mul_apply, Fin.sum_univ_three, matMul, polyEval_append,
    polyEval_polyMul]

/-- The identity matrix of polynomials. -/
def matOne (p q : Fin 3) : LPoly ι :=
  if p = q then [([], [])] else []

theorem matEval_matOne (t : ι → Δ) : matEval t (matOne : LMat ι) = 1 := by
  ext p q
  rw [matEval_apply, matOne, Matrix.one_apply]
  by_cases h : p = q
  · rw [if_pos h, if_pos h, polyEval_unit]
  · rw [if_neg h, if_neg h, polyEval_nil]

/-- The elementary matrix `I + s E_ij` of polynomials. -/
def elemMat (i j : Fin 3) (s : LPoly ι) (p q : Fin 3) : LPoly ι :=
  if p = q then [([], [])] else if p = i ∧ q = j then s else []

theorem val_elementaryUnit {R : Type*} [Ring R] {i j : Fin 3} (h : i ≠ j) (a : R) :
    ((elementaryUnit i j h a : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) =
      1 + Matrix.single i j a :=
  rfl

/-- The entries of `1 + a E_ij`. -/
theorem one_add_single_apply {R : Type*} [Ring R] (i j p q : Fin 3) (a : R) :
    (1 + Matrix.single i j a : Matrix (Fin 3) (Fin 3) R) p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) :=
  rfl

/-- **The letter `(i, j, s)` evaluates to `x_ij(eval s)`.** -/
theorem matEval_elemMat (t : ι → Δ) {i j : Fin 3} (h : i ≠ j) (s : LPoly ι) :
    matEval t (elemMat i j s) =
      ((elementaryUnit i j h (polyEval t s) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ)) := by
  rw [val_elementaryUnit]
  refine Matrix.ext fun p q => Eq.trans ?_ (one_add_single_apply i j p q (polyEval t s)).symm
  rw [matEval_apply, elemMat]
  by_cases hpq : p = q
  · rw [if_pos hpq, if_pos hpq, polyEval_unit,
      if_neg fun e : i = p ∧ j = q => h (e.1.trans (hpq.trans e.2.symm)), add_zero]
  · rw [if_neg hpq, if_neg hpq, zero_add]
    by_cases hij : p = i ∧ q = j
    · rw [if_pos hij, if_pos (⟨hij.1.symm, hij.2.symm⟩ : i = p ∧ j = q)]
    · rw [if_neg hij, polyEval_nil, if_neg fun e : i = p ∧ j = q => hij ⟨e.1.symm, e.2.symm⟩]

/-! ### Characteristic `2` -/

theorem one_add_one_lampRing : (1 + 1 : LampRing Δ) = 0 := by
  have h : (1 + 1 : LocallyConstant (LampSpace Δ) (ZMod 2)) = 0 := LocallyConstant.ext fun x => by
    rw [LocallyConstant.add_apply, LocallyConstant.one_apply, LocallyConstant.zero_apply]
    decide
  rw [← map_one (ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)),
    ← map_add (ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)), h,
    map_zero (ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2))]

/-- `R_Δ` has characteristic `2`. -/
theorem add_self_lampRing (a : LampRing Δ) : a + a = 0 := by
  calc a + a = (1 + 1) * a := by rw [add_mul, one_mul]
    _ = 0 := by rw [one_add_one_lampRing, zero_mul]

theorem eq_iff_add_eq_zero_lampRing (a b : LampRing Δ) : a = b ↔ a + b = 0 := by
  constructor
  · rintro rfl
    exact add_self_lampRing a
  · intro hab
    calc a = a + (b + b) := by rw [add_self_lampRing, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [hab, zero_add]

/-- `1 - a E_ij = 1 + a E_ij` in characteristic `2`. -/
theorem one_sub_single_eq (i j : Fin 3) (a : LampRing Δ) :
    (1 - Matrix.single i j a : Matrix (Fin 3) (Fin 3) (LampRing Δ)) = 1 + Matrix.single i j a := by
  have hself : (Matrix.single i j a : Matrix (Fin 3) (Fin 3) (LampRing Δ)) + Matrix.single i j a = 0 := by
    rw [← Matrix.single_add, add_self_lampRing a, Matrix.single_zero]
  rw [sub_eq_iff_eq_add, add_assoc, hself, add_zero]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.fac_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.termEval_termMul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.matEval_matMul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.matEval_elemMat

end LamplighterWP
end SimpleKazhdanSofic
end GroupApproximation
