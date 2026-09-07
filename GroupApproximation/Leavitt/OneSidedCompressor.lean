import GroupApproximation.Leavitt.OneSidedInverse
import GroupApproximation.Leavitt.ElementaryStabilization
import GroupApproximation.Kazhdan.Kazhdan

/-!
# The rank-four compressor of a one-sided inverse pair

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the middle of the
proof of Theorem `thm:full-defect-ring`:

> For `i = 1,2,3`, set `uᵢ = e₄ᵢ(t-1) eᵢ₄(1) e₄ᵢ(s-1) eᵢ₄(-t)`.  Its block on
> coordinates `(i,4)` is `(s e; 0 t)`, so `u = u₃u₂u₁ ∈ EL₄(R)` is the first of
> the two matrices … In particular `u eᵢⱼ(a) u⁻¹ = eᵢⱼ(sat)` for
> `1 ≤ i ≠ j ≤ 3`, because `e + st = 1`, so `uLu⁻¹ ≤ L`.

Coordinates are 0-indexed here: the core `L = EL₃(R)` occupies `0,1,2` of
`Fin 4` and the compressor's spare coordinate is `3`.  So the printed `u_i` is
`compressorPiece P i` and the printed `u` is `compressor P`.

Everything is over an arbitrary unital ring and uses only `t s = 1`.  The ideal
condition on `1 - st` is used nowhere in this module; it enters in
`GroupApproximation.Leavitt.FullIdempotentNormalGeneration`.  The centralizer
element `c`, the printed defect `d = [ucu⁻¹, ℓ]` and its normal generation are
in `GroupApproximation.Leavitt.OneSidedCompressorDefect`.

The template for the matrix calculations is
`GroupApproximation.Leavitt.RankFourCompressors`, which runs the same four
transvections for a binary Leavitt family; there `e` is spelled `p₁ = s₁t₁`.
-/

namespace GroupApproximation
namespace OneSidedCompressor

universe u w

variable {R : Type u} [Ring R]

/-! ### Associated forms of the one-sided relations

`simp` right-associates products, so the two-factor relations of
`OneSidedInverse` have to be available in the shape `a * (b * x)` as well. -/

namespace OneSidedInverse

variable (P : OneSidedInverse R)

@[simp] theorem assoc_t_mul_s (x : R) : P.t * (P.s * x) = x := by
  rw [← mul_assoc, P.t_mul_s, one_mul]

@[simp] theorem assoc_t_mul_e (x : R) : P.t * (P.e * x) = 0 := by
  rw [← mul_assoc, P.t_mul_e, zero_mul]

@[simp] theorem assoc_e_mul_s (x : R) : P.e * (P.s * x) = 0 := by
  rw [← mul_assoc, P.e_mul_s, zero_mul]

@[simp] theorem assoc_e_mul_e (x : R) : P.e * (P.e * x) = P.e * x := by
  rw [← mul_assoc, P.e_mul_e]

@[simp] theorem st_add_e : P.s * P.t + P.e = 1 := by
  rw [add_comm]
  exact P.e_add_st

end OneSidedInverse

/-! ### The four coordinates -/

/-- The three core coordinates `0,1,2` of `Fin 4`. -/
def coreIdx (i : Fin 3) : Fin 4 := Fin.castSucc i

/-- The spare coordinate `3` of `Fin 4`, the printed fourth coordinate. -/
def lastIdx : Fin 4 := 3

theorem coreIdx_injective : Function.Injective coreIdx := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 4 ↦ x.val) h

theorem last_ne_coreIdx (i : Fin 3) : lastIdx ≠ coreIdx i := by
  intro h
  have hval := congrArg Fin.val h
  simp [lastIdx, coreIdx] at hval
  omega

theorem coreIdx_ne_last (i : Fin 3) : coreIdx i ≠ lastIdx :=
  (last_ne_coreIdx i).symm

/-! ### The core `EL₃(R)` -/

/-- The elementary roots supported on the three core coordinates. -/
def coreRootSet (R : Type u) [Ring R] : Set (elementaryGroup (Fin 4) R) :=
  {x | ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
    elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a = x}

/-- The printed core `L = EL₃(R)`, sitting in coordinates `0,1,2` of
`EL₄(R)`. -/
def core (R : Type u) [Ring R] : Subgroup (elementaryGroup (Fin 4) R) :=
  Subgroup.closure (coreRootSet R)

theorem elementaryRoot_mem_core (i j : Fin 3) (hij : i ≠ j) (a : R) :
    elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a ∈ core R :=
  Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

/-! ### The core as the image of `EL₃(R)` -/

/-- The coordinate equivalence used to reindex the block stabilization. -/
def indexEquiv : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun x := match x with
    | Sum.inl i => Fin.castSucc i
    | Sum.inr _ => 3
  invFun n := if h : n.val < 3 then Sum.inl ⟨n.val, h⟩ else Sum.inr ()
  left_inv := by decide
  right_inv := by decide

@[simp] theorem indexEquiv_inl (i : Fin 3) : indexEquiv (Sum.inl i) = coreIdx i := rfl

/-- The upper-left embedding `EL₃(R) → EL₄(R)`. -/
noncomputable def coreEmbedding :
    elementaryGroup (Fin 3) R →* elementaryGroup (Fin 4) R :=
  (elementaryReindexEquiv (R := R) indexEquiv).toMonoidHom.comp
    (elementaryStabilization (ι := Fin 3) (κ := Unit) (R := R))

theorem coreEmbedding_injective :
    Function.Injective (coreEmbedding (R := R)) :=
  (elementaryReindexEquiv (R := R) indexEquiv).injective.comp
    elementaryStabilization_injective

@[simp] theorem coreEmbedding_elementaryRoot (i j : Fin 3) (hij : i ≠ j) (a : R) :
    coreEmbedding (elementaryRoot i j hij a) =
      elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a := by
  apply Subtype.ext
  change elementaryReindexUnitEquiv (R := R) indexEquiv
      (stabilizeUnit (κ := Unit) (elementaryUnit i j hij a)) =
    elementaryUnit (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a
  rw [stabilizeUnit_elementaryUnit, elementaryReindexUnitEquiv_elementaryUnit]
  rfl

theorem coreEmbedding_mem_core (g : elementaryGroup (Fin 3) R) :
    coreEmbedding g ∈ core R := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      have h : coreEmbedding (elementaryRoot (R := R) i j hij a) ∈ core R := by
        rw [coreEmbedding_elementaryRoot]
        exact elementaryRoot_mem_core i j hij a
      exact h
  | one =>
      rw [show (⟨1, Subgroup.one_mem _⟩ : elementaryGroup (Fin 3) R) = 1 from rfl,
        map_one]
      exact (core R).one_mem
  | mul x y hx hy ihx ihy =>
      rw [show (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : elementaryGroup (Fin 3) R)
          = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
      exact (core R).mul_mem ihx ihy
  | inv x hx ihx =>
      rw [show (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : elementaryGroup (Fin 3) R)
          = (⟨x, hx⟩ : elementaryGroup (Fin 3) R)⁻¹ from rfl, map_inv]
      exact (core R).inv_mem ihx

theorem coreEmbedding_range : (coreEmbedding (R := R)).range = core R := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact coreEmbedding_mem_core g
  · rw [core, Subgroup.closure_le]
    rintro x ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryRoot i j hij a, coreEmbedding_elementaryRoot i j hij a⟩

/-- The upper-left embedding, corestricted to the core. -/
noncomputable def coreEmbeddingToCore :
    elementaryGroup (Fin 3) R →* (core R) :=
  (coreEmbedding (R := R)).codRestrict (core R) coreEmbedding_mem_core

theorem coreEmbeddingToCore_surjective :
    Function.Surjective (coreEmbeddingToCore (R := R)) := by
  intro x
  have hx : (x : elementaryGroup (Fin 4) R) ∈ (coreEmbedding (R := R)).range := by
    rw [coreEmbedding_range]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

/-- Property `(T)` transports from `EL₃(R)` to the printed core. -/
theorem core_hasKazhdanPropertyT
    (h : HasKazhdanPropertyT.{u, w} (elementaryGroup (Fin 3) R)) :
    HasKazhdanPropertyT.{u, w} (core R) :=
  HasKazhdanPropertyT.of_surjective coreEmbeddingToCore
    coreEmbeddingToCore_surjective h

/-! ### The four-transvection pieces -/

/-- The printed factor `uᵢ = e₄ᵢ(t-1) eᵢ₄(1) e₄ᵢ(s-1) eᵢ₄(-t)`, 0-indexed. -/
def compressorPiece (P : OneSidedInverse R) (i : Fin 3) :
    elementaryGroup (Fin 4) R :=
  elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.t - 1) *
    elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) 1 *
      elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.s - 1) *
        elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) (-P.t)

/-- The sparse matrix of one piece: the printed block `(s e; 0 t)` on
coordinates `(i, 3)` and the identity elsewhere. -/
def compressorPieceMatrix (P : OneSidedInverse R) (i : Fin 3) :
    Matrix (Fin 4) (Fin 4) R := fun r c ↦
  if r = coreIdx i then
    if c = coreIdx i then P.s else if c = lastIdx then P.e else 0
  else if r = lastIdx then
    if c = lastIdx then P.t else 0
  else if r = c then 1 else 0

@[simp] theorem compressorPiece_val (P : OneSidedInverse R) (i : Fin 3) :
    (↑(↑(compressorPiece P i) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R)
      = compressorPieceMatrix P i := by
  have hupper : -P.t + (P.t - P.s * P.t) + 1 = P.e := by
    rw [OneSidedInverse.e_eq]
    abel
  have hcancel : P.t - 1 + (P.s - 1 + (1 - P.s - (P.t - 1))) = 0 := by
    abel
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [compressorPiece, compressorPieceMatrix, elementaryRoot, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIdx, lastIdx,
      P.t_mul_s, hupper, hcancel, mul_add, add_mul, mul_sub, sub_mul]

/-! ### The compressor -/

/-- The printed compressor `u = u₃u₂u₁`, as twelve explicit transvections. -/
def compressor (P : OneSidedInverse R) : elementaryGroup (Fin 4) R :=
  compressorPiece P 2 * compressorPiece P 1 * compressorPiece P 0

/-- The first printed display: the matrix of `u`. -/
def compressorMatrix (P : OneSidedInverse R) : Matrix (Fin 4) (Fin 4) R :=
  !![P.s, 0, 0, P.e;
     0, P.s, 0, P.e * P.t;
     0, 0, P.s, P.e * P.t * P.t;
     0, 0, 0, P.t * P.t * P.t]

@[simp] theorem compressor_val (P : OneSidedInverse R) :
    (↑(↑(compressor P) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R)
      = compressorMatrix P := by
  change
    (↑(↑(compressorPiece P 2) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R) *
        (↑(↑(compressorPiece P 1) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
          Matrix (Fin 4) (Fin 4) R) *
          (↑(↑(compressorPiece P 0) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
            Matrix (Fin 4) (Fin 4) R)
      = compressorMatrix P
  rw [compressorPiece_val, compressorPiece_val, compressorPiece_val]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorPieceMatrix, compressorMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, coreIdx, lastIdx, mul_assoc]

/-- The second printed display: the matrix of `u⁻¹`. -/
def compressorInvMatrix (P : OneSidedInverse R) : Matrix (Fin 4) (Fin 4) R :=
  !![P.t, 0, 0, 0;
     0, P.t, 0, 0;
     0, 0, P.t, 0;
     P.e, P.s * P.e, P.s * P.s * P.e, P.s * P.s * P.s]

theorem compressorMatrix_mul_inv (P : OneSidedInverse R) :
    compressorMatrix P * compressorInvMatrix P = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorMatrix, compressorInvMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_assoc, P.t_mul_s]

theorem compressor_inv_val (P : OneSidedInverse R) :
    ((((compressor P : (Matrix (Fin 4) (Fin 4) R)ˣ))⁻¹ :
          (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = compressorInvMatrix P :=
  Units.inv_eq_of_mul_eq_one_right
    (by rw [compressor_val]; exact compressorMatrix_mul_inv P)

theorem compressorInvMatrix_mul (P : OneSidedInverse R) :
    compressorInvMatrix P * compressorMatrix P = 1 := by
  have h := Units.inv_mul (compressor P : (Matrix (Fin 4) (Fin 4) R)ˣ)
  rwa [compressor_inv_val, compressor_val] at h

/-! ### Conjugation of the core -/

/-- The printed identity `u eᵢⱼ(a) u⁻¹ = eᵢⱼ(sat)`, in multiplicative form. -/
theorem compressor_mul_coreRoot (P : OneSidedInverse R)
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    compressor P *
        elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a =
      elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij)
          (P.s * a * P.t) * compressor P := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [elementaryRoot, elementaryUnit, compressorMatrix, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, coreIdx, P.t_mul_s, mul_assoc]

/-- The printed identity `u eᵢⱼ(a) u⁻¹ = eᵢⱼ(sat)` for `i ≠ j` in the core. -/
theorem compressor_conj_root (P : OneSidedInverse R)
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    compressor P *
        elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a *
        (compressor P)⁻¹ =
      elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij)
        (P.s * a * P.t) := by
  rw [compressor_mul_coreRoot P i j hij a]
  group

/-- **The printed conclusion `uLu⁻¹ ≤ L`.** -/
theorem compressor_compresses_core (P : OneSidedInverse R) :
    ∀ g ∈ core R, compressor P * g * (compressor P)⁻¹ ∈ core R := by
  intro g hg
  rw [core] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [compressor_conj_root P i j hij a]
      exact elementaryRoot_mem_core i j hij (P.s * a * P.t)
  | one => simp
  | mul x y _ _ hx hy =>
      have h : compressor P * (x * y) * (compressor P)⁻¹ =
          (compressor P * x * (compressor P)⁻¹) *
            (compressor P * y * (compressor P)⁻¹) := by group
      rw [h]
      exact (core R).mul_mem hx hy
  | inv x _ hx =>
      have h : compressor P * x⁻¹ * (compressor P)⁻¹ =
          (compressor P * x * (compressor P)⁻¹)⁻¹ := by group
      rw [h]
      exact (core R).inv_mem hx

end OneSidedCompressor
end GroupApproximation
