import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Vectors

/-!
# Block decomposition of last-column stabilizers in `St_{m+1}(B)`

This is a leaf of the relative rank-four Brown criterion (Khanh, arXiv:2609.08428, Thm 5.1). That
criterion is used on the Leavitt route to `simple_kazhdan_sofic_group.tex` l.733-735
(`sec:questions`).

Let `u ∈ St_m(B)` and `v ∈ Bᵐ`. The image of `castSuccStab u * rowVec v` in `E_{m+1}(B)` has the
block form `[[A, 0], [v, 1]]`, where `A` is the image of `u`:
* `elMat_stabRow_apply` computes every entry of that image.
* `stabRow_decomp` shows that a matrix with last column `e_last` arises this way once its top
  block is realised.
* `stabRow_ker` shows that the image is trivial only when `v = 1` and `u` projects to `1`.
* `stabRow m B` is the subgroup of all products `castSuccStab u * rowVec v`, and
  `x_mem_stabRow` shows that it contains every root `x_{ij}` with `j ≠ m`.
* `topBlockUnit` is the invertible top block of a unit whose last column, and whose inverse's
  last column, is `e_last` above the diagonal.
-/

namespace GroupApproximation
namespace Full
namespace LVRelBrown

open SteinbergGroup ElementarySimplicity ElementaryPadding LVCentral

variable {B : Type*} [Ring B] {m : ℕ}

/-! ### Entries of the padding along `Fin.castSucc` -/

theorem last_not_mem_range :
    Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
  rintro ⟨j, hj⟩
  exact Fin.castSucc_ne_last j hj

theorem padEquiv_symm_castSucc (j : Fin m) :
    (padEquiv (Fin.castSuccEmb : Fin m ↪ Fin (m + 1))).symm j.castSucc = Sum.inl j :=
  (Equiv.symm_apply_eq _).mpr rfl

theorem padEquiv_symm_last :
    (padEquiv (Fin.castSuccEmb : Fin m ↪ Fin (m + 1))).symm (Fin.last m) =
      Sum.inr ⟨Fin.last m, last_not_mem_range⟩ :=
  (Equiv.symm_apply_eq _).mpr rfl

theorem padHom_castSucc (M : Matrix (Fin m) (Fin m) B) (i j : Fin m) :
    padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) M i.castSucc j.castSucc = M i j := by
  rw [padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, padEquiv_symm_castSucc,
    padEquiv_symm_castSucc, Matrix.fromBlocks_apply₁₁]

theorem padHom_last_left (M : Matrix (Fin m) (Fin m) B) (q : Fin (m + 1)) :
    padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) M (Fin.last m) q =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (Fin.last m) q := by
  rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
  · rw [padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, padEquiv_symm_last,
      padEquiv_symm_castSucc, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
  · rw [padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, padEquiv_symm_last,
      Matrix.fromBlocks_apply₂₂]
    simp only [Matrix.one_apply_eq]

theorem padHom_last_right (M : Matrix (Fin m) (Fin m) B) (p : Fin (m + 1)) :
    padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) M p (Fin.last m) =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) p (Fin.last m) := by
  rcases Fin.eq_castSucc_or_eq_last p with ⟨i, rfl⟩ | rfl
  · rw [padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, padEquiv_symm_castSucc,
      padEquiv_symm_last, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      Matrix.one_apply_ne (Fin.castSucc_ne_last i)]
  · exact padHom_last_left M (Fin.last m)

theorem elMat_projection_castSuccStab (u : SteinbergGroup (Fin m) B) :
    elMat (projection (castSuccStab m B u)) =
      padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) (elMat (projection u)) :=
  (congrArg elMat (projection_castSuccStab u)).trans rfl

theorem mul_rowMatrix_apply (P : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (p₀ : Fin (m + 1))
    (w : Fin (m + 1) → B) (p q : Fin (m + 1)) :
    (P * rowMatrix p₀ w) p q = P p p₀ * w q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p₀]
  · rw [rowMatrix_apply, if_pos rfl]
  · intro k _ hk
    rw [rowMatrix_apply, if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p₀) h

/-! ### The block decomposition -/

/-- Entries of the image of `castSuccStab u * rowVec v`. -/
theorem elMat_stabRow_apply (u : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B)
    (p q : Fin (m + 1)) :
    elMat (projection (castSuccStab m B u * rowVec v)) p q =
      padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) (elMat (projection u)) p q +
        padHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) (elMat (projection u)) p (Fin.last m) *
          padVec v q := by
  rw [map_mul, elMat_mul, elMat_projection_castSuccStab, elMat_projection_rowVec,
    mul_add, mul_one, Matrix.add_apply, mul_rowMatrix_apply]

/-- The last row of a matrix, without its last entry, as a multiplicative vector. -/
def lastRowVec (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) : Fin m → Multiplicative B :=
  fun j => Multiplicative.ofAdd (g (Fin.last m) j.castSucc)

/-- A matrix with last column `e_last` is the image of `castSuccStab u * rowVec v` once `u`
realises its top block. -/
theorem stabRow_decomp (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (hcol : ∀ i : Fin m, g i.castSucc (Fin.last m) = 0) (hlast : g (Fin.last m) (Fin.last m) = 1)
    (u : SteinbergGroup (Fin m) B)
    (hu : ∀ i j : Fin m, elMat (projection u) i j = g i.castSucc j.castSucc) :
    elMat (projection (castSuccStab m B u * rowVec (lastRowVec g))) = g := by
  ext p q
  rw [elMat_stabRow_apply]
  rcases Fin.eq_castSucc_or_eq_last p with ⟨i, rfl⟩ | rfl
  · rw [padHom_last_right _ i.castSucc, Matrix.one_apply_ne (Fin.castSucc_ne_last i), zero_mul,
      add_zero]
    rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · rw [padHom_castSucc, hu]
    · rw [padHom_last_right _ i.castSucc, Matrix.one_apply_ne (Fin.castSucc_ne_last i), hcol]
  · rw [padHom_last_right _ (Fin.last m), Matrix.one_apply_eq, one_mul]
    rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · rw [padHom_last_left _ j.castSucc, Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm,
        zero_add]
      exact padVec_castSucc (lastRowVec g) j
    · rw [padHom_last_left _ (Fin.last m), Matrix.one_apply_eq, padVec_last, add_zero, hlast]

/-- The image of `castSuccStab u * rowVec v` is trivial only when `v = 1` and `u` projects
to `1`. -/
theorem stabRow_ker (u : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B)
    (h : elMat (projection (castSuccStab m B u * rowVec v)) = 1) :
    v = 1 ∧ projection u = 1 := by
  constructor
  · funext j
    have hj := congrFun (congrFun h (Fin.last m)) j.castSucc
    rw [elMat_stabRow_apply, padHom_last_left _ j.castSucc, padHom_last_right _ (Fin.last m),
      Matrix.one_apply_eq, one_mul, padVec_castSucc,
      Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm, zero_add] at hj
    exact Multiplicative.toAdd.injective hj
  · apply elMat_injective
    rw [elMat_one]
    ext i j
    have hij := congrFun (congrFun h i.castSucc) j.castSucc
    rw [elMat_stabRow_apply, padHom_castSucc, padHom_last_right _ i.castSucc,
      Matrix.one_apply_ne (Fin.castSucc_ne_last i), zero_mul, add_zero] at hij
    rw [hij]
    by_cases hne : i = j
    · subst hne
      simp only [Matrix.one_apply_eq]
    · have hne' : i.castSucc ≠ j.castSucc := fun h' => hne (Fin.castSucc_inj.mp h')
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hne']

/-! ### The subgroup `St_m(B) ⋉ Bᵐ` -/

/-- The subgroup of products `castSuccStab u * rowVec v`. -/
def stabRow (m : ℕ) (B : Type*) [Ring B] : Subgroup (SteinbergGroup (Fin (m + 1)) B) where
  carrier := {g | ∃ (u : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B),
    castSuccStab m B u * rowVec v = g}
  mul_mem' := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
    obtain ⟨w, hw⟩ := rowVec_conj u'⁻¹ v
    refine ⟨u * u', w * v', ?_⟩
    simp only [map_mul]
    rw [← hw]
    simp only [map_inv, inv_inv]
    group
  one_mem' := ⟨1, 1, by simp only [map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨w, hw⟩ := rowVec_conj u v⁻¹
    refine ⟨u⁻¹, w, ?_⟩
    rw [← hw]
    simp only [map_inv]
    group

theorem mem_stabRow {g : SteinbergGroup (Fin (m + 1)) B} :
    g ∈ stabRow m B ↔ ∃ (u : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B),
      castSuccStab m B u * rowVec v = g :=
  Iff.rfl

/-- Every root `x_{ij}(a)` with `j ≠ m` lies in `stabRow m B`. -/
theorem x_mem_stabRow (i j : Fin (m + 1)) (hij : i ≠ j) (hj : j ≠ Fin.last m) (a : B) :
    x i j hij a ∈ stabRow m B := by
  obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hj
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · refine mem_stabRow.mpr ⟨x i' j' (fun h => hij (congrArg Fin.castSucc h)) a, 1, ?_⟩
    simp only [map_one, mul_one, castSuccStab_x]
  · refine mem_stabRow.mpr ⟨1, Pi.mulSingle j' (Multiplicative.ofAdd a), ?_⟩
    simp only [map_one, one_mul, rowVec_mulSingle, toAdd_ofAdd]

/-! ### Top blocks -/

/-- The top-left `m × m` block of an `(m+1) × (m+1)` matrix. -/
def topBlock (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) : Matrix (Fin m) (Fin m) B :=
  g.submatrix Fin.castSucc Fin.castSucc

theorem topBlock_apply (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (i j : Fin m) :
    topBlock g i j = g i.castSucc j.castSucc :=
  rfl

theorem topBlock_mul (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (hg : ∀ i : Fin m, g i.castSucc (Fin.last m) = 0) :
    topBlock (g * h) = topBlock g * topBlock h := by
  ext i j
  simp only [topBlock_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hg i, zero_mul, add_zero]

theorem topBlock_one : topBlock (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) = 1 :=
  Matrix.submatrix_one _ (Fin.castSucc_injective m)

/-- The top block of a unit whose last column, and whose inverse's last column, vanish above
the diagonal. -/
def topBlockUnit (g : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ)
    (hg : ∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) i.castSucc (Fin.last m) = 0)
    (hg' : ∀ i : Fin m,
      ((g⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
        i.castSucc (Fin.last m) = 0) :
    (Matrix (Fin m) (Fin m) B)ˣ where
  val := topBlock (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
  inv := topBlock ((g⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) B)
  val_inv := by rw [← topBlock_mul _ _ hg, Units.mul_inv, topBlock_one]
  inv_val := by rw [← topBlock_mul _ _ hg', Units.inv_mul, topBlock_one]

theorem topBlockUnit_val (g : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ)
    (hg : ∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) i.castSucc (Fin.last m) = 0)
    (hg' : ∀ i : Fin m,
      ((g⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) B)ˣ) : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
        i.castSucc (Fin.last m) = 0) (i j : Fin m) :
    ((topBlockUnit g hg hg' : (Matrix (Fin m) (Fin m) B)ˣ) : Matrix (Fin m) (Fin m) B) i j =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) B) i.castSucc j.castSucc :=
  rfl

end LVRelBrown
end Full
end GroupApproximation
