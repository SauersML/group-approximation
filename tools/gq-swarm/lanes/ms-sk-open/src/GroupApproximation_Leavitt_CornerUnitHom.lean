import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner matrices `(1 - p) I_n + h`

`non_mf_groups_exist.tex`, proof of `thm:core-mf-radical`:

> If $g\in\GL_n(R_X)$ restricts to the identity, put all entries of $g-1$ and $g^{-1}-1$
> inside one finite matrix-product algebra $B=\prod_a M_{h_a}(\F_2)\subset I$, with local
> identity $p$.  Then $g=(1-p)I_n+h$ with $h\in\GL_n(B)$.

The subalgebra `B ⊆ R` is the image of an injective non-unital ring hom `φ : A →ₙ+* R` from a
unital ring `A`, and its local identity is `p = φ 1`.  Since `(1 - p) φ(a) = 0 = φ(a) (1 - p)`,

* `cornerMatrixHom φ : Matrix ι ι A →* Matrix ι ι R`, `M ↦ (1 - p) I + M.map φ`, is a monoid hom;
* `cornerUnitHom φ : GL_n(A) →* GL_n(R)` is the induced map on units, it sends the root `x_{ij}(a)`
  to the root `x_{ij}(φ a)` (`cornerUnitHom_elementaryUnit`), so it maps `EL_n(A)` into `EL_n(R)`;
* both are injective when `φ` is (`cornerMatrixHom_injective`, `cornerUnitHom_injective`);
* `exists_cornerUnitHom_eq`: if all entries of `g - 1` and `g⁻¹ - 1` lie in the range of `φ`,
  then `g = (1 - p) I_n + h` for a unit `h` of `M_n(A)`, i.e. `g = cornerUnitHom φ h`.
-/

namespace GroupApproximation
namespace ChainRadical

variable {ι A R : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Ring R] (φ : A →ₙ+* R)

theorem one_sub_map_one_mul (a : A) : (1 - φ 1) * φ a = 0 := by
  rw [sub_mul, one_mul, ← map_mul φ, one_mul, sub_self]

theorem map_mul_one_sub_map_one (a : A) : φ a * (1 - φ 1) = 0 := by
  rw [mul_sub, mul_one, ← map_mul φ, mul_one, sub_self]

/-- The local identity `p = φ 1` is idempotent, so `1 - p` is. -/
theorem one_sub_map_one_mul_self : (1 - φ 1) * (1 - φ 1) = 1 - φ 1 := by
  rw [mul_sub, mul_one, one_sub_map_one_mul, sub_zero]

theorem map_one_eq_scalar : (1 : Matrix ι ι A).map φ = Matrix.scalar ι (φ 1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_map (map_zero φ), Matrix.scalar_apply]

theorem scalar_one_sub_mul_map (M : Matrix ι ι A) :
    Matrix.scalar ι (1 - φ 1) * M.map φ = 0 := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, one_sub_map_one_mul,
    Matrix.zero_apply]

theorem map_mul_scalar_one_sub (M : Matrix ι ι A) :
    M.map φ * Matrix.scalar ι (1 - φ 1) = 0 := by
  rw [Matrix.scalar_apply, ← Matrix.op_smul_eq_mul_diagonal]
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, op_smul_eq_mul, map_mul_one_sub_map_one,
    Matrix.zero_apply]

omit [DecidableEq ι] in
theorem map_mul_map (M N : Matrix ι ι A) : M.map φ * N.map φ = (M * N).map φ := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

/-- **`M ↦ (1 - p) I + M.map φ`, `p = φ 1`, is a monoid hom.** -/
def cornerMatrixHom : Matrix ι ι A →* Matrix ι ι R where
  toFun M := Matrix.scalar ι (1 - φ 1) + M.map φ
  map_one' := by
    change Matrix.scalar ι (1 - φ 1) + (1 : Matrix ι ι A).map φ = 1
    rw [map_one_eq_scalar, ← map_add (Matrix.scalar ι), sub_add_cancel, map_one (Matrix.scalar ι)]
  map_mul' M N := by
    change Matrix.scalar ι (1 - φ 1) + (M * N).map φ =
      (Matrix.scalar ι (1 - φ 1) + M.map φ) * (Matrix.scalar ι (1 - φ 1) + N.map φ)
    rw [add_mul, mul_add, mul_add, ← map_mul (Matrix.scalar ι), one_sub_map_one_mul_self,
      scalar_one_sub_mul_map, map_mul_scalar_one_sub, map_mul_map, add_zero, zero_add]

theorem cornerMatrixHom_apply (M : Matrix ι ι A) :
    cornerMatrixHom φ M = Matrix.scalar ι (1 - φ 1) + M.map φ := rfl

theorem cornerMatrixHom_one_add (M : Matrix ι ι A) :
    cornerMatrixHom φ (1 + M) = 1 + M.map φ := by
  rw [cornerMatrixHom_apply, Matrix.map_add _ (map_add φ), map_one_eq_scalar, ← add_assoc,
    ← map_add (Matrix.scalar ι), sub_add_cancel, map_one (Matrix.scalar ι)]

/-- **Corner matrices are injective when `φ` is.** -/
theorem cornerMatrixHom_injective (hφ : Function.Injective φ) :
    Function.Injective (cornerMatrixHom (ι := ι) φ) := fun M N h ↦ by
  have h' : Matrix.scalar ι (1 - φ 1) + M.map φ = Matrix.scalar ι (1 - φ 1) + N.map φ := h
  exact Matrix.map_injective hφ (add_left_cancel h')

/-- The induced map `GL_n(A) →* GL_n(R)`, `h ↦ (1 - p) I_n + h`. -/
def cornerUnitHom : (Matrix ι ι A)ˣ →* (Matrix ι ι R)ˣ :=
  Units.map (cornerMatrixHom φ)

theorem cornerUnitHom_injective (hφ : Function.Injective φ) :
    Function.Injective (cornerUnitHom (ι := ι) φ) := fun _ _ h ↦
  Units.ext (cornerMatrixHom_injective φ hφ (congrArg Units.val h))

/-- **The root `x_{ij}(a)` goes to the root `x_{ij}(φ a)`.** -/
theorem cornerUnitHom_elementaryUnit (i j : ι) (hij : i ≠ j) (a : A) :
    cornerUnitHom φ (elementaryUnit i j hij a) = elementaryUnit i j hij (φ a) := by
  apply Units.ext
  change cornerMatrixHom φ (1 + Matrix.single i j a) = 1 + Matrix.single i j (φ a)
  rw [cornerMatrixHom_one_add, Matrix.map_single]

theorem elementaryGroup_map_cornerUnitHom_le :
    (elementaryGroup ι A).map (cornerUnitHom φ) ≤ elementaryGroup ι R := by
  refine Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le (K := _)).2 ?_)
  rintro _ ⟨i, j, hij, a, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [cornerUnitHom_elementaryUnit]
  exact elementaryUnit_mem i j hij (φ a)

/-- **`g = (1 - p) I_n + h` with `h ∈ GL_n(A)`** when the entries of `g - 1` and `g⁻¹ - 1` lie
in the range of the injective `φ`. -/
theorem exists_cornerUnitHom_eq (hφ : Function.Injective φ) (g : (Matrix ι ι R)ˣ)
    (hg : ∀ k l, ∃ x, φ x = ((g : Matrix ι ι R) - 1) k l)
    (hg' : ∀ k l, ∃ x, φ x = (((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) k l) :
    ∃ h : (Matrix ι ι A)ˣ, cornerUnitHom φ h = g := by
  choose X hX using hg
  choose Y hY using hg'
  have hU : cornerMatrixHom φ (1 + Matrix.of X) = g := by
    rw [cornerMatrixHom_one_add]
    ext k l
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hX, Matrix.sub_apply, add_sub_cancel]
  have hV : cornerMatrixHom φ (1 + Matrix.of Y) = ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
    rw [cornerMatrixHom_one_add]
    ext k l
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hY, Matrix.sub_apply, add_sub_cancel]
  refine ⟨⟨1 + Matrix.of X, 1 + Matrix.of Y, ?_, ?_⟩, Units.ext hU⟩
  · refine cornerMatrixHom_injective φ hφ ?_
    rw [map_mul, hU, hV, map_one, Units.mul_inv]
  · refine cornerMatrixHom_injective φ hφ ?_
    rw [map_mul, hU, hV, map_one, Units.inv_mul]

end ChainRadical
end GroupApproximation

#audit_axioms GroupApproximation.ChainRadical.cornerMatrixHom
#audit_axioms GroupApproximation.ChainRadical.cornerMatrixHom_injective
#audit_axioms GroupApproximation.ChainRadical.cornerUnitHom_injective
#audit_axioms GroupApproximation.ChainRadical.cornerUnitHom_elementaryUnit
#audit_axioms GroupApproximation.ChainRadical.elementaryGroup_map_cornerUnitHom_le
#audit_axioms GroupApproximation.ChainRadical.exists_cornerUnitHom_eq
