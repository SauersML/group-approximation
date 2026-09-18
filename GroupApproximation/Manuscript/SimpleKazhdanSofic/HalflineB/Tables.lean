import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterRing
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): tables for the elements of `R_Δ = LC(Ω, F₂) ⋊ Λ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b), tex l.657–661 (sentence 7bfa078c0bed):

> A word in the generators of G_Δ multiplies out to a matrix with entries Σ_ξ p_ξ u_ξ, where each p_ξ is a
> polynomial over F_2 in finitely many coordinates x(δ), as u_ξ e_U u_ξ^{-1} is the indicator of
> {x : x(δ) = 1 + c(δ)} for ξ : x ↦ δx + c.

and tex l.661–664 (sentence e3cd35e16e2f, the collection of equal `ξ`):

> After collecting equal ξ and equal coordinates, the word is trivial if and only if every coefficient of its
> difference from I_3 vanishes at every assignment of its finitely many variables, as Ω is the full shift.

## Proof route

* A table is a finite list of monomials `(a, [p₁, …, pₙ])`, words `a, p_k` in the generators `z`, `t i` of `Λ`. It
  stands for `Σ (e_U ∘ ξ_{p₁}⁻¹) ⋯ (e_U ∘ ξ_{pₙ}⁻¹) u_{ξ_a}` (`hTabEval`), where `ξ_w` is the value of `w`.
* The product of monomials is a monomial (`hMonoEval_mul`), by `u_ξ f = (f ∘ ξ⁻¹) u_ξ` and
  `e_U ∘ ξ_p⁻¹ ∘ ξ_a⁻¹ = e_U ∘ ξ_{ap}⁻¹` (`comap_hAtom`). So products of tables and of matrices of tables are
  the ring products (`hTabEval_hTabMul`, `hMatEval_hMatMul`).
* An atom is `x ↦ x(δ) + c(δ)` for `ξ_p = inl c · inr δ` (`hAtom_apply`): the indicator of `{x(δ) = 1 + c(δ)}`.
* Collecting equal `ξ` (`hCoeffLC`, `coeff_hTabEval`): a table vanishes iff the sum of the monomials with value
  `ξ_a` vanishes at every point, for every monomial `a` of the table (`hTabEval_eq_zero_iff`).
* In characteristic two, `r = r'` iff `r + r' = 0` (`lampRing_eq_iff_add_eq_zero`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter
open SkewMonoidAlgebra (single)

/-- A word in the generators `z` (`none`) and `t i` (`some i`) of `Λ`. -/
abbrev LW (ι : Type) : Type := List (Option ι × Bool)

/-- A monomial `(a, [p₁, …, pₙ])`. -/
abbrev HMono (ι : Type) : Type := LW ι × List (LW ι)

/-- A table: a finite sum of monomials. -/
abbrev HTable (ι : Type) : Type := List (HMono ι)

/-- A `3 × 3` matrix of tables. -/
abbrev HMat (ι : Type) : Type := Fin 3 → Fin 3 → HTable ι

variable {Δ : Type} [Group Δ] {ι : Type}

/-- The atom of a word `p`: `e_U ∘ ξ_p⁻¹`, for `e_U` the coordinate at `1`. -/
noncomputable def hAtom (s : ι → Δ) (p : LW ι) : LocallyConstant (LampSpace Δ) (ZMod 2) :=
  LocallyConstant.comap
    (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen s) p)⁻¹) (coord Δ 1)

/-- The product of the atoms of a list of words. -/
noncomputable def hCyl (s : ι → Δ) : List (LW ι) → LocallyConstant (LampSpace Δ) (ZMod 2)
  | [] => 1
  | p :: P => hAtom s p * hCyl s P

/-- The value `(e_U ∘ ξ_{p₁}⁻¹) ⋯ (e_U ∘ ξ_{pₙ}⁻¹) u_{ξ_a}` of a monomial. -/
noncomputable def hMonoEval (s : ι → Δ) (m : HMono ι) : LampRing Δ :=
  single (wordValue (lampGen s) m.1) (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s m.2))

/-- The value of a table. -/
noncomputable def hTabEval (s : ι → Δ) (T : HTable ι) : LampRing Δ :=
  (T.map (hMonoEval s)).sum

/-- The entrywise value of a matrix of tables. -/
noncomputable def hMatEval (s : ι → Δ) (M : HMat ι) : Matrix (Fin 3) (Fin 3) (LampRing Δ) :=
  Matrix.of fun i j => hTabEval s (M i j)

/-- The product of monomials: `(a, P) · (a', P') = (a a', P ++ a P')`. -/
def hMonoMul (m m' : HMono ι) : HMono ι :=
  (m.1 ++ m'.1, m.2 ++ m'.2.map fun p => m.1 ++ p)

/-- The product of tables. -/
def hTabMul (T T' : HTable ι) : HTable ι :=
  T.flatMap fun m => T'.map (hMonoMul m)

/-- The product of matrices of tables. -/
def hMatMul (M N : HMat ι) (i j : Fin 3) : HTable ι :=
  hTabMul (M i 0) (N 0 j) ++ hTabMul (M i 1) (N 1 j) ++ hTabMul (M i 2) (N 2 j)

/-- The identity matrix of tables. -/
def hMatOne (i j : Fin 3) : HTable ι :=
  if i = j then [([], [])] else []

/-! ### Products -/

theorem comap_hAtom (s : ι → Δ) (a p : LW ι) :
    LocallyConstant.comap
        (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen s) a)⁻¹) (hAtom s p) =
      hAtom s (a ++ p) := by
  ext x
  simp only [hAtom, LocallyConstant.coe_comap_apply, ClopenGroupCoeff.smulMap_apply]
  rw [wordValue_append, mul_inv_rev, mul_smul]

theorem comap_hCyl (s : ι → Δ) (a : LW ι) (P : List (LW ι)) :
    LocallyConstant.comap
        (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen s) a)⁻¹) (hCyl s P) =
      hCyl s (P.map fun p => a ++ p) := by
  induction P with
  | nil =>
    rw [List.map_nil, hCyl]
    ext x
    rfl
  | cons p P ih =>
    rw [List.map_cons, hCyl, hCyl, ← comap_hAtom s a p, ← ih]
    ext x
    rfl

theorem hCyl_append (s : ι → Δ) (P P' : List (LW ι)) : hCyl s (P ++ P') = hCyl s P * hCyl s P' := by
  induction P with
  | nil => rw [List.nil_append, hCyl, one_mul]
  | cons p P ih => rw [List.cons_append, hCyl, hCyl, ih, mul_assoc]

theorem hMonoEval_mul (s : ι → Δ) (m m' : HMono ι) :
    hMonoEval s m * hMonoEval s m' = hMonoEval s (hMonoMul m m') := by
  show single (wordValue (lampGen s) m.1)
        (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s m.2)) *
      single (wordValue (lampGen s) m'.1)
        (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s m'.2)) =
    single (wordValue (lampGen s) (m.1 ++ m'.1))
      (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s (m.2 ++ m'.2.map fun p => m.1 ++ p)))
  rw [SkewMonoidAlgebra.single_mul_single, ClopenGroupCoeff.smul_of,
    ← map_mul (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)), comap_hCyl, hCyl_append,
    wordValue_append]

theorem hTabEval_nil (s : ι → Δ) : hTabEval s ([] : HTable ι) = 0 := by
  simp only [hTabEval, List.map_nil, List.sum_nil]

theorem hTabEval_cons (s : ι → Δ) (m : HMono ι) (T : HTable ι) :
    hTabEval s (m :: T) = hMonoEval s m + hTabEval s T := by
  simp only [hTabEval, List.map_cons, List.sum_cons]

theorem hTabEval_append (s : ι → Δ) (T T' : HTable ι) :
    hTabEval s (T ++ T') = hTabEval s T + hTabEval s T' := by
  simp only [hTabEval, List.map_append, List.sum_append]

theorem hTabEval_map_hMonoMul (s : ι → Δ) (m : HMono ι) (T' : HTable ι) :
    hTabEval s (T'.map (hMonoMul m)) = hMonoEval s m * hTabEval s T' := by
  induction T' with
  | nil => rw [List.map_nil, hTabEval_nil, mul_zero]
  | cons m' T' ih => rw [List.map_cons, hTabEval_cons, hTabEval_cons, ih, mul_add, hMonoEval_mul]

/-- **The table product is the ring product.** -/
theorem hTabEval_hTabMul (s : ι → Δ) (T T' : HTable ι) :
    hTabEval s (hTabMul T T') = hTabEval s T * hTabEval s T' := by
  unfold hTabMul
  induction T with
  | nil => rw [List.flatMap_nil, hTabEval_nil, zero_mul]
  | cons m T ih => rw [List.flatMap_cons, hTabEval_append, hTabEval_map_hMonoMul, ih, hTabEval_cons, add_mul]

theorem hMatEval_apply (s : ι → Δ) (M : HMat ι) (i j : Fin 3) : hMatEval s M i j = hTabEval s (M i j) :=
  rfl

/-- **The matrix product of tables is the matrix product.** -/
theorem hMatEval_hMatMul (s : ι → Δ) (M N : HMat ι) : hMatEval s (hMatMul M N) = hMatEval s M * hMatEval s N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [hMatEval_apply, Matrix.mul_apply, Fin.sum_univ_three, hMatMul, hTabEval_append, hTabEval_hTabMul]

theorem hTabEval_unit (s : ι → Δ) : hTabEval s ([([], [])] : HTable ι) = 1 := by
  rw [hTabEval_cons, hTabEval_nil, add_zero]
  show single (wordValue (lampGen s) ([] : LW ι))
      (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s [])) = 1
  rw [wordValue_nil, hCyl, map_one, SkewMonoidAlgebra.single_one_one]

theorem hMatEval_hMatOne (s : ι → Δ) : hMatEval s (hMatOne : HMat ι) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  rw [hMatEval_apply, hMatOne, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, hTabEval_unit]
  · rw [if_neg h, if_neg h, hTabEval_nil]

/-! ### Characteristic two -/

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> decide

theorem lampRing_one_add_one : (1 + 1 : LampRing Δ) = 0 := by
  have h : (1 + 1 : LocallyConstant (LampSpace Δ) (ZMod 2)) = 0 :=
    LocallyConstant.ext fun x => by
      rw [LocallyConstant.add_apply, LocallyConstant.one_apply, LocallyConstant.zero_apply]
      decide
  have e := congrArg (ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)) h
  rwa [map_add, map_one, map_zero] at e

theorem lampRing_add_self (r : LampRing Δ) : r + r = 0 := by
  rw [← one_mul r, ← add_mul, lampRing_one_add_one, zero_mul]

theorem lampRing_eq_iff_add_eq_zero (r r' : LampRing Δ) : r = r' ↔ r + r' = 0 := by
  constructor
  · rintro rfl
    exact lampRing_add_self r
  · intro h
    calc r = r + (r' + r') := by rw [lampRing_add_self, add_zero]
      _ = (r + r') + r' := (add_assoc r r' r').symm
      _ = r' := by rw [h, zero_add]

/-! ### Collecting equal `ξ` -/

open Classical in
/-- The sum of the atom products of the monomials with value `η`. -/
noncomputable def hCoeffLC (s : ι → Δ) (η : LampAffine Δ) : HTable ι → LocallyConstant (LampSpace Δ) (ZMod 2)
  | [] => 0
  | m :: T => (if wordValue (lampGen s) m.1 = η then hCyl s m.2 else 0) + hCoeffLC s η T

open Classical in
theorem coeff_hMonoEval (s : ι → Δ) (m : HMono ι) (η : LampAffine Δ) :
    SkewMonoidAlgebra.coeff (hMonoEval s m) η =
      ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)
        (if wordValue (lampGen s) m.1 = η then hCyl s m.2 else 0) := by
  rw [hMonoEval, SkewMonoidAlgebra.coeff_single]
  by_cases h : wordValue (lampGen s) m.1 = η
  · rw [if_pos h, h, Finsupp.single_eq_same]
  · rw [if_neg h, map_zero, Finsupp.single_eq_of_ne fun e => h e.symm]

/-- **The coefficient of `u_η`** of a table. -/
theorem coeff_hTabEval (s : ι → Δ) (T : HTable ι) (η : LampAffine Δ) :
    SkewMonoidAlgebra.coeff (hTabEval s T) η =
      ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCoeffLC s η T) := by
  induction T with
  | nil => rw [hTabEval_nil, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hCoeffLC, map_zero]
  | cons m T ih =>
    rw [hTabEval_cons, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, ih, coeff_hMonoEval, hCoeffLC, map_add]

theorem hCoeffLC_eq_zero (s : ι → Δ) {η : LampAffine Δ} {T : HTable ι}
    (h : ∀ m ∈ T, wordValue (lampGen s) m.1 ≠ η) : hCoeffLC s η T = 0 := by
  induction T with
  | nil => rw [hCoeffLC]
  | cons m T ih =>
    rw [hCoeffLC, if_neg (h m List.mem_cons_self), ih fun m' hm' => h m' (List.mem_cons_of_mem m hm'), add_zero]

/-- **A table vanishes** iff, for every monomial `(a, P)` of it, the sum of the atom products of the monomials with
value `ξ_a` vanishes at every point of `Ω`. -/
theorem hTabEval_eq_zero_iff (s : ι → Δ) (T : HTable ι) :
    hTabEval s T = 0 ↔ ∀ m0 ∈ T, ∀ x, hCoeffLC s (wordValue (lampGen s) m0.1) T x = 0 := by
  constructor
  · intro h m0 _ x
    have hc := coeff_hTabEval s T (wordValue (lampGen s) m0.1)
    rw [h, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    have hf : hCoeffLC s (wordValue (lampGen s) m0.1) T = 0 :=
      (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).injective
        (hc.symm.trans (map_zero (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2))).symm)
    rw [hf, LocallyConstant.zero_apply]
  · intro h
    refine SkewMonoidAlgebra.ext fun η => ?_
    rw [coeff_hTabEval, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hη : ∃ m0 ∈ T, wordValue (lampGen s) m0.1 = η
    · obtain ⟨m0, hm0, rfl⟩ := hη
      have hf : hCoeffLC s (wordValue (lampGen s) m0.1) T = 0 :=
        LocallyConstant.ext fun x => (h m0 hm0 x).trans (LocallyConstant.zero_apply x).symm
      rw [hf, map_zero]
    · rw [hCoeffLC_eq_zero s fun m hm e => hη ⟨m, hm, e⟩, map_zero]

/-! ### Point values -/

open Classical in
theorem hCoeffLC_apply (s : ι → Δ) (η : LampAffine Δ) (T : HTable ι) (x : LampSpace Δ) :
    hCoeffLC s η T x = (T.map fun m => if wordValue (lampGen s) m.1 = η then hCyl s m.2 x else 0).sum := by
  induction T with
  | nil => rw [hCoeffLC, List.map_nil, List.sum_nil, LocallyConstant.zero_apply]
  | cons m T ih =>
    rw [hCoeffLC, LocallyConstant.add_apply, ih, List.map_cons, List.sum_cons]
    by_cases hm : wordValue (lampGen s) m.1 = η
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, LocallyConstant.zero_apply]

theorem hCyl_apply (s : ι → Δ) (P : List (LW ι)) (x : LampSpace Δ) :
    hCyl s P x = (P.map fun p => hAtom s p x).prod := by
  induction P with
  | nil => rw [hCyl, List.map_nil, List.prod_nil, LocallyConstant.one_apply]
  | cons p P ih => rw [hCyl, LocallyConstant.mul_apply, ih, List.map_cons, List.prod_cons]

/-- `(inl c · inr δ) • y` at `δ` is `y(1) + c(δ)`. -/
theorem smul_apply_right (c : Δ →₀ ZMod 2) (δ : Δ) (y : LampSpace Δ) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd c) * SemidirectProduct.inr δ : LampAffine Δ) • y) δ =
      y 1 + c δ := by
  rw [Lamplighter.smul_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr, one_mul,
    inv_mul_cancel, SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
    SemidirectProduct.right_inl, map_one, mul_one, toAdd_ofAdd]

/-- **The atom of `p` is `x ↦ x(δ) + c(δ)`** for `ξ_p = inl c · inr δ` (tex l.659–660): the indicator of
`{x : x(δ) = 1 + c(δ)}`. -/
theorem hAtom_apply (s : ι → Δ) (p : LW ι) (x : LampSpace Δ) :
    hAtom s p x = x (wordValue s (deltaWord p)) + lampSum s p (wordValue s (deltaWord p)) := by
  rw [hAtom, LocallyConstant.coe_comap_apply, ClopenGroupCoeff.smulMap_apply, coord_apply]
  have hx := smul_apply_right (lampSum s p) (wordValue s (deltaWord p)) ((wordValue (lampGen s) p)⁻¹ • x)
  rw [← wordValue_lampGen, smul_inv_smul] at hx
  rw [hx, add_assoc, zmod_two_add_self, add_zero]

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.hMatEval_hMatMul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.hTabEval_eq_zero_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.hAtom_apply
