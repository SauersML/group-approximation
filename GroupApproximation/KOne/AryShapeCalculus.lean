import GroupApproximation.Leavitt.AryWindowReduction
import GroupApproximation.KOne.DegreeShapeBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The rectangular shape calculus, at arbitrary arity

`KOne/ShapeCalculus.lean` and the shape half of `KOne/DegreeShapeBridge.lean` over a
complete matrix family `F` on an alphabet `ι`: an element of the span of the
shape-`(p, q)` monomials `s_γ t_δ` (`|γ| = p`, `|δ| = q`) is `Σ M γ δ • s_γ t_δ` for a
unique scalar matrix `M`, entries are recovered by compression `t_γ · x · s_δ`, and the
assignment is multiplicative at matching interfaces.  Degree-`j` elements lie in the
shape spans `(q + j, q)` at every deep interface `q`.  This is the engine behind the rank
arguments of the keystone `AryZeroKOne`: degree-`j` elements are
`|ι|^{q+j} × |ι|^q`-shaped, so composites through low interfaces have small rank.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- The monomials of shape `(p, q)`: `s`-word of length `p`, `t`-word of length `q`. -/
def shapeMonomials (p q : ℕ) : Set A :=
  {x | ∃ (f : Fin p → ι) (g : Fin q → ι),
    x = F.wordS (List.ofFn f) * F.wordT (List.ofFn g)}

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- An element is *shape-represented* by a scalar matrix when it is the corresponding
combination of shape monomials. -/
def ShapeRep (p q : ℕ) (M : Matrix (Fin p → ι) (Fin q → ι) k) (x : A) : Prop :=
  x = ∑ γ : Fin p → ι, ∑ δ : Fin q → ι,
    M γ δ • (F.wordS (List.ofFn γ) * F.wordT (List.ofFn δ))

theorem shapeRep_mem_span {p q : ℕ} {M : Matrix (Fin p → ι) (Fin q → ι) k} {x : A}
    (h : F.ShapeRep p q M x) :
    x ∈ Submodule.span k (F.shapeMonomials p q) := by
  rw [h]
  exact Submodule.sum_mem _ fun γ _ ↦ Submodule.sum_mem _ fun δ _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, δ, rfl⟩)

/-- Every element of the shape span has a representing matrix. -/
theorem exists_shapeRep {p q : ℕ} {x : A}
    (hx : x ∈ Submodule.span k (F.shapeMonomials p q)) :
    ∃ M : Matrix (Fin p → ι) (Fin q → ι) k, F.ShapeRep p q M x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨f, g, rfl⟩ := hxmem
      refine ⟨Matrix.single f g 1, ?_⟩
      unfold ShapeRep
      rw [Finset.sum_eq_single f, Finset.sum_eq_single g]
      · simp [Matrix.single]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hg
        exact absurd (Finset.mem_univ g) hg
      · intro b _ hb
        refine Finset.sum_eq_zero fun δ _ ↦ ?_
        simp [Ne.symm hb]
      · intro hf
        exact absurd (Finset.mem_univ f) hf
  | zero => exact ⟨0, by simp [ShapeRep]⟩
  | add x y _ _ hx hy =>
      obtain ⟨M, hM⟩ := hx
      obtain ⟨N, hN⟩ := hy
      refine ⟨M + N, ?_⟩
      unfold ShapeRep at hM hN ⊢
      rw [hM, hN, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      rw [Matrix.add_apply, add_smul]
  | smul r x _ hx =>
      obtain ⟨M, hM⟩ := hx
      refine ⟨r • M, ?_⟩
      unfold ShapeRep at hM ⊢
      rw [hM, Finset.smul_sum]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      rw [Matrix.smul_apply, smul_smul, smul_eq_mul]

/-- Entry extraction: compressing a represented element between equal-length words
recovers the matrix entry. -/
theorem shapeRep_entry {p q : ℕ} {M : Matrix (Fin p → ι) (Fin q → ι) k} {x : A}
    (h : F.ShapeRep p q M x) (γ : Fin p → ι) (δ : Fin q → ι) :
    F.wordT (List.ofFn γ) * x * F.wordS (List.ofFn δ) = algebraMap k A (M γ δ) := by
  classical
  have hterm : ∀ (a : Fin p → ι) (b : Fin q → ι),
      F.wordT (List.ofFn γ) *
        (M a b • (F.wordS (List.ofFn a) * F.wordT (List.ofFn b))) *
        F.wordS (List.ofFn δ) =
      M a b • ((F.wordT (List.ofFn γ) * F.wordS (List.ofFn a)) *
        (F.wordT (List.ofFn b) * F.wordS (List.ofFn δ))) := by
    intro a b
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    noncomm_ring
  calc F.wordT (List.ofFn γ) * x * F.wordS (List.ofFn δ)
      = ∑ a : Fin p → ι, ∑ b : Fin q → ι,
          F.wordT (List.ofFn γ) *
            (M a b • (F.wordS (List.ofFn a) * F.wordT (List.ofFn b))) *
            F.wordS (List.ofFn δ) := by
        rw [h, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a : Fin p → ι, ∑ b : Fin q → ι,
          M a b • (((if γ = a then (1 : A) else 0)) *
            (if b = δ then (1 : A) else 0)) := by
        refine Finset.sum_congr rfl fun a _ ↦
          Finset.sum_congr rfl fun b _ ↦ ?_
        rw [hterm a b, F.powerFamily_orthogonal p γ a, F.powerFamily_orthogonal q b δ]
    _ = algebraMap k A (M γ δ) := by
        rw [Finset.sum_eq_single γ, Finset.sum_eq_single δ]
        · simp [Algebra.smul_def]
        · intro b _ hb
          simp [if_neg hb]
        · intro hδ
          exact absurd (Finset.mem_univ δ) hδ
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ ↦ ?_
          simp [if_neg (Ne.symm ha)]
        · intro hγ
          exact absurd (Finset.mem_univ γ) hγ

/-- Uniqueness of the representing matrix, given that scalars embed. -/
theorem shapeRep_unique {p q : ℕ} (hinj : Function.Injective (algebraMap k A))
    {M N : Matrix (Fin p → ι) (Fin q → ι) k} {x : A}
    (hM : F.ShapeRep p q M x) (hN : F.ShapeRep p q N x) : M = N := by
  funext γ δ
  refine hinj ?_
  rw [← F.shapeRep_entry hM γ δ, ← F.shapeRep_entry hN γ δ]

/-- The unit is represented by the identity matrix at every square shape. -/
theorem shapeRep_one (n : ℕ) : F.ShapeRep n n (1 : Matrix _ _ k) 1 := by
  classical
  unfold ShapeRep
  rw [← F.sum_cylinder_ofFn n]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [Finset.sum_eq_single γ]
  · rw [Matrix.one_apply_eq, one_smul, cylinder]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  · intro hγ
    exact absurd (Finset.mem_univ γ) hγ

/-- Multiplicativity at matching interfaces. -/
theorem shapeRep_mul {p q r : ℕ} {M : Matrix (Fin p → ι) (Fin q → ι) k}
    {N : Matrix (Fin q → ι) (Fin r → ι) k} {x y : A}
    (hM : F.ShapeRep p q M x) (hN : F.ShapeRep q r N y) :
    F.ShapeRep p r (M * N) (x * y) := by
  classical
  unfold ShapeRep at hM hN ⊢
  rw [hM, hN, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [Finset.sum_mul]
  calc ∑ δ : Fin q → ι,
        (M γ δ • (F.wordS (List.ofFn γ) * F.wordT (List.ofFn δ))) *
        ∑ δ' : Fin q → ι, ∑ ε : Fin r → ι,
          N δ' ε • (F.wordS (List.ofFn δ') * F.wordT (List.ofFn ε))
      = ∑ δ : Fin q → ι, ∑ δ' : Fin q → ι, ∑ ε : Fin r → ι,
          (M γ δ * N δ' ε) •
            (F.wordS (List.ofFn γ) *
              (F.wordT (List.ofFn δ) * F.wordS (List.ofFn δ')) *
              F.wordT (List.ofFn ε)) := by
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ' _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        noncomm_ring
    _ = ∑ δ : Fin q → ι, ∑ ε : Fin r → ι,
          (M γ δ * N δ ε) • (F.wordS (List.ofFn γ) * F.wordT (List.ofFn ε)) := by
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [Finset.sum_eq_single δ]
        · rw [F.powerFamily_orthogonal q δ δ, if_pos rfl, mul_one]
        · intro δ' _ hδ'
          rw [F.powerFamily_orthogonal q δ δ', if_neg (Ne.symm hδ')]
          rw [show F.wordS (List.ofFn γ) * (0 : A) * F.wordT (List.ofFn ε) = 0 from by
            noncomm_ring, smul_zero]
        · intro hδ
          exact absurd (Finset.mem_univ δ) hδ
    _ = ∑ ε : Fin r → ι, (M * N) γ ε •
          (F.wordS (List.ofFn γ) * F.wordT (List.ofFn ε)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [Matrix.mul_apply, Finset.sum_smul]

/-- Sums of representing matrices represent sums. -/
theorem shapeRep_add {p q : ℕ} {M N : Matrix (Fin p → ι) (Fin q → ι) k} {x y : A}
    (hM : F.ShapeRep p q M x) (hN : F.ShapeRep p q N y) :
    F.ShapeRep p q (M + N) (x + y) := by
  unfold ShapeRep at hM hN ⊢
  rw [hM, hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  rw [Matrix.add_apply, add_smul]

/-- Finite sums of representing matrices represent finite sums. -/
theorem shapeRep_finsetSum {p q : ℕ} {γι : Type*} (s : Finset γι)
    (M : γι → Matrix (Fin p → ι) (Fin q → ι) k) (x : γι → A)
    (h : ∀ i ∈ s, F.ShapeRep p q (M i) (x i)) :
    F.ShapeRep p q (∑ i ∈ s, M i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold ShapeRep
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact F.shapeRep_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end Scalars

section Padding

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Shape spans pad: splitting the trailing cylinder rewrites a shape-`(p, q)` monomial
as a sum of shape-`(p+1, q+1)` monomials. -/
theorem span_shapeMonomials_le_succ (p q : ℕ) :
    Submodule.span k (F.shapeMonomials p q) ≤
      Submodule.span k (F.shapeMonomials (p + 1) (q + 1)) := by
  rw [Submodule.span_le]
  rintro x ⟨f, g, rfl⟩
  rw [F.wordS_mul_wordT_split (List.ofFn f) (List.ofFn g)]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ?_
  refine ⟨Fin.snoc f i, Fin.snoc g i, ?_⟩
  have hsnoc : ∀ (m : ℕ) (h : Fin m → ι), List.ofFn (Fin.snoc h i) = List.ofFn h ++ [i] := by
    intro m h
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  rw [hsnoc p f, hsnoc q g]

/-- A monomial lies in every shape span obtained by padding both words by a common
depth. -/
theorem monomial_mem_shapeSpan (a b : List ι) (r : ℕ) :
    F.wordS a * F.wordT b ∈
      Submodule.span k (F.shapeMonomials (a.length + r) (b.length + r)) := by
  induction r with
  | zero =>
      exact Submodule.subset_span ⟨a.get, b.get, by rw [List.ofFn_get, List.ofFn_get]⟩
  | succ r ih =>
      exact F.span_shapeMonomials_le_succ (a.length + r) (b.length + r) ih

/-- **Degree spans embed in shape spans**: an element of pure degree `j` lies in the
shape span `(p, q)` for every deep enough interface `q` with `(p : ℤ) = q + j`. -/
theorem exists_shapeSpan_of_degreeSpan {j : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials j j)) :
    ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q → (p : ℤ) = (q : ℤ) + j →
      x ∈ Submodule.span k (F.shapeMonomials p q) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine ⟨b.length, fun p q hq hpq ↦ ?_⟩
      have hj : (a.length : ℤ) - b.length = j := le_antisymm hh hl
      have h := F.monomial_mem_shapeSpan (k := k) a b (q - b.length)
      have hp : a.length + (q - b.length) = p := by omega
      have hq2 : b.length + (q - b.length) = q := by omega
      rw [hp, hq2] at h
      exact h
  | zero => exact ⟨0, fun p q _ _ ↦ Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨nx, hnx⟩ := hx
      obtain ⟨ny, hny⟩ := hy
      exact ⟨max nx ny, fun p q hq hpq ↦ Submodule.add_mem _
        (hnx p q (le_trans (le_max_left _ _) hq) hpq)
        (hny p q (le_trans (le_max_right _ _) hq) hpq)⟩
  | smul r x _ hx =>
      obtain ⟨nx, hnx⟩ := hx
      exact ⟨nx, fun p q hq hpq ↦ Submodule.smul_mem _ r (hnx p q hq hpq)⟩

end Padding

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_shapeRep
#audit_axioms GroupApproximation.CompleteMatrixFamily.shapeRep_entry
#audit_axioms GroupApproximation.CompleteMatrixFamily.shapeRep_unique
#audit_axioms GroupApproximation.CompleteMatrixFamily.shapeRep_one
#audit_axioms GroupApproximation.CompleteMatrixFamily.shapeRep_mul
#audit_axioms GroupApproximation.CompleteMatrixFamily.shapeRep_finsetSum
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_shapeSpan_of_degreeSpan
