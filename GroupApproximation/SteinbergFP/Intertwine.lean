import GroupApproximation.SteinbergFP.Swap

/-!
# The block swap intertwines the base copy with the doubled copy

Let `U = Fin 3 × V`.  The base copy `σ : V ↪ U`, `i ↦ (0, i)`, and the doubled copy
`δ : V × Fin 2 ↪ U`, `(i, s) ↦ (s, i)`, are related by the block swap
`ω = diagMap (swap L) ∈ St_U(S)`, whose elementary matrix is the block-diagonal
`W = diag(W₁, …, W₁)`:

    π(ω · σ(g) · ω⁻¹) = π(δ(double L g))   for every g ∈ St_V(S)   (`stMatrix_conj_swap`).

On generators this is the matrix identity `W (1 + e_{σi,σj}(a)) = (1 + Σ_{s,u} e_{(s,i),(u,j)}(t_s a s_u)) W`,
which uses only `s₀ t₀ + s₁ t₁ = 1`.  This is steps (c)–(d) of the research node
`leavitt-pairs-embed-sl-n-q-in-steinberg-groups`, with the elementary square swap of
`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open SteinbergGroup

variable {V S : Type*} [Fintype V] [DecidableEq V] [Ring S] (L : LeavittFamily S)

/-- The base copy `i ↦ (0, i)`. -/
def baseEmb : V ↪ Fin 3 × V := ⟨fun i ↦ (0, i), fun _ _ h ↦ (Prod.mk.inj h).2⟩

/-- The doubled copy `(i, s) ↦ (s, i)`. -/
def dblEmb : V × Fin 2 ↪ Fin 3 × V :=
  ⟨fun p ↦ (Fin.castSucc p.2, p.1), fun p q h ↦ by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext h2 (Fin.castSucc_injective _ h1)⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem baseEmb_apply (i : V) : baseEmb (V := V) i = (0, i) := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem dblEmb_apply (i : V) (s : Fin 2) : dblEmb (V := V) (i, s) = (Fin.castSucc s, i) :=
  rfl

/-- The block swap. -/
def blockSwap : SteinbergGroup (Fin 3 × V) S := diagMap (V := V) (swap L)

/-- Its elementary matrix. -/
abbrev swapBlockMatrix : Matrix (Fin 3 × V) (Fin 3 × V) S :=
  Matrix.blockDiagonal (fun _ : V ↦ swapMatrix L)

theorem stMatrix_blockSwap :
    stMatrix (Fin 3 × V) S (blockSwap (V := V) L) = swapBlockMatrix (V := V) L := by
  rw [blockSwap, stMatrix_diagMap, stMatrix_swap]

theorem swapMatrix_castSucc_row (u : Fin 2) (b : Fin 3) :
    swapMatrix L (Fin.castSucc u) b = if b = 0 then L.tv u else 0 := by
  fin_cases u <;> fin_cases b <;> simp [swapMatrix, LeavittFamily.tv]

theorem swap_mul_single (i j : V) (a : S) :
    swapBlockMatrix (V := V) L * Matrix.single (0, i) (0, j) a =
      Matrix.single (0, i) (0, j) (L.t0 * a) + Matrix.single (1, i) (0, j) (L.t1 * a) := by
  unfold swapBlockMatrix
  ext ⟨α, k⟩ ⟨β, l⟩
  rw [Matrix.add_apply]
  by_cases hq : ((β, l) : Fin 3 × V) = (0, j)
  · rw [hq, Matrix.mul_single_apply_same, Matrix.blockDiagonal_apply]
    by_cases hk : k = i
    · subst hk
      fin_cases α <;> simp [swapMatrix]
    · simp [hk, Ne.symm hk]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.single_apply, Matrix.single_apply,
      if_neg, if_neg, add_zero]
    all_goals exact fun h ↦ hq h.2.symm

theorem single_mul_swap (i j : V) (s u : Fin 2) (c : S) :
    Matrix.single (Fin.castSucc s, i) (Fin.castSucc u, j) c * swapBlockMatrix (V := V) L =
      Matrix.single (Fin.castSucc s, i) (0, j) (c * L.tv u) := by
  unfold swapBlockMatrix
  ext ⟨α, k⟩ ⟨β, l⟩
  by_cases hp : ((α, k) : Fin 3 × V) = (Fin.castSucc s, i)
  · rw [hp, Matrix.single_mul_apply_same, Matrix.blockDiagonal_apply, Matrix.single_apply]
    by_cases hl : j = l
    · subst hl
      rw [if_pos rfl, swapMatrix_castSucc_row]
      by_cases hb : β = 0
      · subst hb
        simp
      · simp [hb, Ne.symm hb]
    · rw [if_neg hl, mul_zero, if_neg]
      exact fun h ↦ hl (Prod.mk.inj h.2).2
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp, Matrix.single_apply, if_neg]
    exact fun h ↦ hp h.1.symm

/-- `(1 + E₁)(1 + E₂)(1 + E₃)(1 + E₄) = 1 + ΣEᵢ` when all products `EᵢEⱼ` (`i < j`) vanish. -/
theorem prod_one_add_of_mul_zero {R : Type*} [Ring R] (E₁ E₂ E₃ E₄ : R) (h12 : E₁ * E₂ = 0)
    (h13 : E₁ * E₃ = 0) (h14 : E₁ * E₄ = 0) (h23 : E₂ * E₃ = 0) (h24 : E₂ * E₄ = 0)
    (h34 : E₃ * E₄ = 0) :
    (1 + E₁) * (1 + E₂) * (1 + E₃) * (1 + E₄) = 1 + (E₁ + E₂ + E₃ + E₄) := by
  have s1 : (1 + E₁) * (1 + E₂) = 1 + (E₁ + E₂) := by
    calc (1 + E₁) * (1 + E₂) = 1 + (E₁ + E₂) + E₁ * E₂ := by noncomm_ring
      _ = 1 + (E₁ + E₂) := by rw [h12, add_zero]
  have s2 : (1 + (E₁ + E₂)) * (1 + E₃) = 1 + (E₁ + E₂ + E₃) := by
    calc (1 + (E₁ + E₂)) * (1 + E₃) = 1 + (E₁ + E₂ + E₃) + (E₁ * E₃ + E₂ * E₃) := by
          noncomm_ring
      _ = 1 + (E₁ + E₂ + E₃) := by rw [h13, h23, add_zero, add_zero]
  have s3 : (1 + (E₁ + E₂ + E₃)) * (1 + E₄) = 1 + (E₁ + E₂ + E₃ + E₄) := by
    calc (1 + (E₁ + E₂ + E₃)) * (1 + E₄) =
          1 + (E₁ + E₂ + E₃ + E₄) + (E₁ * E₄ + E₂ * E₄ + E₃ * E₄) := by noncomm_ring
      _ = 1 + (E₁ + E₂ + E₃ + E₄) := by rw [h14, h24, h34, add_zero, add_zero, add_zero]
  rw [s1, s2, s3]

/-- The elementary matrix of the doubled root. -/
theorem stMatrix_dbl_blk {i j : V} (hij : i ≠ j) (a : S) :
    stMatrix (Fin 3 × V) S (indexMap (dblEmb (V := V)) (blk hij (L.psi a))) =
      1 + (Matrix.single (0, i) (0, j) (L.psi a 0 0) + Matrix.single (0, i) (1, j) (L.psi a 0 1) +
        Matrix.single (1, i) (0, j) (L.psi a 1 0) + Matrix.single (1, i) (1, j) (L.psi a 1 1)) := by
  simp only [blk, dx, map_mul, indexMap_x, stMatrix_x, dblEmb_apply, Fin.castSucc_zero,
    Fin.castSucc_one]
  have hz : ∀ (s u s' u' : Fin 3) (c c' : S),
      Matrix.single ((s, i) : Fin 3 × V) (u, j) c * Matrix.single (s', i) (u', j) c' = 0 :=
    fun _ _ _ _ _ _ ↦
      Matrix.single_mul_single_of_ne _ _ _ _ (fun h ↦ hij (Prod.mk.inj h).2.symm) _
  exact prod_one_add_of_mul_zero _ _ _ _ (hz _ _ _ _ _ _) (hz _ _ _ _ _ _) (hz _ _ _ _ _ _)
    (hz _ _ _ _ _ _) (hz _ _ _ _ _ _) (hz _ _ _ _ _ _)

theorem swap_intertwine {i j : V} (hij : i ≠ j) (a : S) :
    swapBlockMatrix (V := V) L * (1 + Matrix.single (0, i) (0, j) a) =
      stMatrix (Fin 3 × V) S (indexMap (dblEmb (V := V)) (blk hij (L.psi a))) *
        swapBlockMatrix (V := V) L := by
  rw [stMatrix_dbl_blk L hij a, mul_add, mul_one, swap_mul_single, add_mul, one_mul, add_mul,
    add_mul, add_mul]
  have h00 := single_mul_swap L i j 0 0 (L.psi a 0 0)
  have h01 := single_mul_swap L i j 0 1 (L.psi a 0 1)
  have h10 := single_mul_swap L i j 1 0 (L.psi a 1 0)
  have h11 := single_mul_swap L i j 1 1 (L.psi a 1 1)
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h00 h01 h10 h11
  rw [h00, h01, h10, h11]
  have hsum : ∀ c : S, c * L.s0 * L.t0 + c * L.s1 * L.t1 = c := fun c ↦ by
    rw [mul_assoc, mul_assoc, ← mul_add, L.sum_range, mul_one]
  have e0 : L.psi a 0 0 * L.tv 0 + L.psi a 0 1 * L.tv 1 = L.t0 * a := by
    simp only [LeavittFamily.psi, Matrix.of_apply, LeavittFamily.tv, LeavittFamily.sv,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hsum (L.t0 * a)
  have e1 : L.psi a 1 0 * L.tv 0 + L.psi a 1 1 * L.tv 1 = L.t1 * a := by
    simp only [LeavittFamily.psi, Matrix.of_apply, LeavittFamily.tv, LeavittFamily.sv,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hsum (L.t1 * a)
  rw [← e0, ← e1, Matrix.single_add, Matrix.single_add]
  abel

/-- `g ↦ π(ω σ(g) ω⁻¹)`. -/
def conjBase : SteinbergGroup V S →* Matrix (Fin 3 × V) (Fin 3 × V) S :=
  (stMatrix (Fin 3 × V) S).comp
    ((MulAut.conj (blockSwap (V := V) L)).toMonoidHom.comp (indexMap (baseEmb (V := V))))

/-- `g ↦ π(δ(double L g))`. -/
def dblProj : SteinbergGroup V S →* Matrix (Fin 3 × V) (Fin 3 × V) S :=
  (stMatrix (Fin 3 × V) S).comp ((indexMap (dblEmb (V := V))).comp (double L))

theorem conjBase_eq_dblProj : conjBase (V := V) L = dblProj L := by
  apply hom_ext_of_x
  intro i j hij a
  change stMatrix (Fin 3 × V) S (blockSwap L * indexMap baseEmb (x i j hij a) * (blockSwap L)⁻¹) =
    stMatrix (Fin 3 × V) S (indexMap dblEmb (double L (x i j hij a)))
  have hinv : stMatrix (Fin 3 × V) S (blockSwap (V := V) L) *
      stMatrix (Fin 3 × V) S (blockSwap (V := V) L)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, indexMap_x, stMatrix_x, double_x, stMatrix_blockSwap]
  rw [stMatrix_blockSwap] at hinv
  simp only [baseEmb_apply]
  rw [swap_intertwine L hij a, mul_assoc, hinv, mul_one]

/-- **The swap intertwines the base copy with the doubled copy, on elementary matrices.** -/
theorem stMatrix_conj_swap (g : SteinbergGroup V S) :
    stMatrix (Fin 3 × V) S (blockSwap L * indexMap (baseEmb (V := V)) g * (blockSwap L)⁻¹) =
      stMatrix (Fin 3 × V) S (indexMap (dblEmb (V := V)) (double L g)) :=
  DFunLike.congr_fun (conjBase_eq_dblProj L) g

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.stMatrix_conj_swap
