import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.CompressMatrix
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVEGen.GLEqElementary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive

/-!
# Compression of coordinate `0` on Steinberg groups

Steinberg part of the stability step of leaf T1b.iii
(`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`; Khanh, arXiv:2609.08428).

For a binary Leavitt family `F` in a ring `A`, the scalars `dL, dR` of `CompressMatrix.lean`
satisfy `dR k * dL k = 1`, so `x_{ij}(a) ↦ x_{ij}(dL i · a · dR j)` respects the Steinberg
relations.  This gives an endomorphism `steinbergCompress F p` of `St_p(A)` (`κ̃`), and:

* `steinbergCompress_indexMap_castLE`: `κ̃` commutes with identity padding;
* `compressUnits_steinbergToGL_indexMap`: for `L = L_k(1,2)`, the leaf isomorphism
  `δ : GL_{p+1}(L) → GL_p(L)` satisfies `δ ∘ π_{p+1} ∘ pad = π_p ∘ κ̃`;
* `projection_steinbergCompress_eq_one`: `κ̃` maps `K₂(p, L)` into itself;
* `steinbergToGL_steinbergCompress_steinbergCompress`: `π_p ∘ κ̃ ∘ κ̃ = Ad(g) ∘ π_p ∘ κ̃`,
  where `g = diag(w, 1, …, 1)` and `w` is Khanh's conjugating unit.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation
namespace Full
namespace LVStability

open SteinbergGroup
open scoped commutatorElement

variable {A : Type*} [Ring A] (F : LeavittFamily A)

section Generic

variable {p : ℕ}

theorem dL_castLEEmb {q : ℕ} (h : p ≤ q) (r : Fin p) : dL F (Fin.castLEEmb h r) = dL F r :=
  rfl

theorem dR_castLEEmb {q : ℕ} (h : p ≤ q) (r : Fin p) : dR F (Fin.castLEEmb h r) = dR F r :=
  rfl

theorem compress_scalar_mul (i j l : Fin p) (a b : A) :
    dL F i * a * dR F j * (dL F j * b * dR F l) = dL F i * (a * b) * dR F l := by
  calc dL F i * a * dR F j * (dL F j * b * dR F l)
        = dL F i * a * (dR F j * dL F j) * b * dR F l := by simp only [mul_assoc]
    _ = dL F i * (a * b) * dR F l := by
        rw [dR_mul_dL F j, mul_one]
        simp only [mul_assoc]

/-- The image of a Steinberg generator under compression of coordinate `0`. -/
def compressGenerator (g : SteinbergGenerator (Fin p) A) : SteinbergGroup (Fin p) A :=
  x g.row g.column g.row_ne_column (dL F g.row * g.coefficient * dR F g.column)

private theorem compressGenerator_kills_relations
    (w : FreeGroup (SteinbergGenerator (Fin p) A))
    (hw : w ∈ relations (I := Fin p) (R := A)) :
    FreeGroup.lift (compressGenerator F) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, compressGenerator]
      change x i j hij (dL F i * a * dR F j) * x i j hij (dL F i * b * dR F j) *
        (x i j hij (dL F i * (a + b) * dR F j))⁻¹ = 1
      rw [x_mul, ← add_mul, ← mul_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, compressGenerator]
      change ⁅x i j hij (dL F i * a * dR F j), x k l hkl (dL F k * b * dR F l)⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        compressGenerator]
      change ⁅x i j hij (dL F i * a * dR F j), x j k hjk (dL F j * b * dR F k)⁆ *
        (x i k hik (dL F i * (a * b) * dR F k))⁻¹ = 1
      rw [x_commutator i j k hij hjk hik, compress_scalar_mul F i j k a b, mul_inv_cancel]

variable (p) in
/-- **Compression of coordinate `0`** on `St_p(A)`: `x_{ij}(a) ↦ x_{ij}(dL i · a · dR j)`. -/
def steinbergCompress : SteinbergGroup (Fin p) A →* SteinbergGroup (Fin p) A :=
  PresentedGroup.toGroup (f := compressGenerator F) (compressGenerator_kills_relations F)

@[simp] theorem steinbergCompress_x (i j : Fin p) (hij : i ≠ j) (a : A) :
    steinbergCompress F p (x i j hij a) = x i j hij (dL F i * a * dR F j) := by
  exact PresentedGroup.toGroup.of _

/-- Compression commutes with identity padding `St_p(A) → St_q(A)`. -/
theorem steinbergCompress_indexMap_castLE {q : ℕ} (h : p ≤ q) (y : SteinbergGroup (Fin p) A) :
    steinbergCompress F q (indexMap (Fin.castLEEmb h) y) =
      indexMap (Fin.castLEEmb h) (steinbergCompress F p y) := by
  have hh : (steinbergCompress F q).comp (indexMap (R := A) (Fin.castLEEmb h)) =
      (indexMap (Fin.castLEEmb h)).comp (steinbergCompress F p) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change steinbergCompress F q (indexMap (Fin.castLEEmb h) (x i j hij a)) =
      indexMap (Fin.castLEEmb h) (steinbergCompress F p (x i j hij a))
    rw [indexMap_x, steinbergCompress_x, steinbergCompress_x, indexMap_x, dL_castLEEmb,
      dR_castLEEmb]
  exact DFunLike.congr_fun hh y

end Generic

section Diagonal

variable {p : ℕ}

theorem diag_mul_single_mul_diag (d e : Fin p → A) (a b : Fin p) (c : A) :
    Matrix.diagonal d * Matrix.single a b c * Matrix.diagonal e =
      Matrix.single a b (d a * c * e b) := by
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = r ∧ b = s
  · rw [if_pos h, if_pos h, h.1, h.2]
  · rw [if_neg h, if_neg h, mul_zero, zero_mul]

/-- The invertible diagonal matrix with diagonal entries `u r`. -/
def diagMatrixUnit (u : Fin p → Aˣ) : (Matrix (Fin p) (Fin p) A)ˣ where
  val := Matrix.diagonal fun r => (u r : A)
  inv := Matrix.diagonal fun r => (((u r)⁻¹ : Aˣ) : A)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul, Matrix.diagonal_one]

theorem diagMatrixUnit_mul_elementaryUnit_mul_inv (u : Fin p → Aˣ) (i j : Fin p) (hij : i ≠ j)
    (b : A) :
    diagMatrixUnit u * elementaryUnit i j hij b * (diagMatrixUnit u)⁻¹ =
      elementaryUnit i j hij ((u i : A) * b * (((u j)⁻¹ : Aˣ) : A)) := by
  refine Units.ext ?_
  change Matrix.diagonal (fun r => (u r : A)) * (1 + Matrix.single i j b) *
      Matrix.diagonal (fun r => (((u r)⁻¹ : Aˣ) : A)) =
    1 + Matrix.single i j ((u i : A) * b * (((u j)⁻¹ : Aˣ) : A))
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
    diag_mul_single_mul_diag]
  simp only [Units.mul_inv, Matrix.diagonal_one]

/-- The unit at coordinate `r`: Khanh's conjugating unit `w` at `r = 0`, and `1` elsewhere. -/
def coordConjUnit (r : Fin p) : Aˣ :=
  if (r : ℕ) = 0 then LVSuperperfect.compressionConjUnit F else 1

theorem coordConjUnit_mul_dL (r : Fin p) :
    ((coordConjUnit F r : Aˣ) : A) * dL F r = dL F r * dL F r := by
  by_cases h : (r : ℕ) = 0
  · rw [coordConjUnit, if_pos h, dL_of_eq F h]
    exact compressionConjUnit_val_mul_s0 F
  · rw [coordConjUnit, if_neg h, dL_of_ne F h, Units.val_one]

theorem dR_mul_coordConjUnit_inv (r : Fin p) :
    dR F r * (((coordConjUnit F r)⁻¹ : Aˣ) : A) = dR F r * dR F r := by
  by_cases h : (r : ℕ) = 0
  · rw [coordConjUnit, if_pos h, dR_of_eq F h]
    exact t0_mul_compressionConjUnit_inv F
  · rw [coordConjUnit, if_neg h, dR_of_ne F h, inv_one, Units.val_one]

theorem coordConj_scalar (i j : Fin p) (b : A) :
    ((coordConjUnit F i : Aˣ) : A) * (dL F i * b * dR F j) *
        (((coordConjUnit F j)⁻¹ : Aˣ) : A) =
      dL F i * (dL F i * b * dR F j) * dR F j := by
  calc ((coordConjUnit F i : Aˣ) : A) * (dL F i * b * dR F j) *
          (((coordConjUnit F j)⁻¹ : Aˣ) : A)
        = ((coordConjUnit F i : Aˣ) : A) * dL F i * b *
            (dR F j * (((coordConjUnit F j)⁻¹ : Aˣ) : A)) := by simp only [mul_assoc]
    _ = dL F i * dL F i * b * (dR F j * dR F j) := by
        rw [coordConjUnit_mul_dL, dR_mul_coordConjUnit_inv]
    _ = dL F i * (dL F i * b * dR F j) * dR F j := by simp only [mul_assoc]

end Diagonal

section Units

variable {p : ℕ}

/-- The leaf isomorphism `δ : GL_{p+1}(A) → GL_p(A)`, `X ↦ compA X compB`. -/
def compressUnits (hp : 0 < p) :
    (Matrix (Fin (p + 1)) (Fin (p + 1)) A)ˣ →* (Matrix (Fin p) (Fin p) A)ˣ :=
  Units.map (compressMatrixHom F hp)

/-- Its inverse `ε : GL_p(A) → GL_{p+1}(A)`, `Y ↦ compB Y compA`. -/
def expandUnits (hp : 0 < p) :
    (Matrix (Fin p) (Fin p) A)ˣ →* (Matrix (Fin (p + 1)) (Fin (p + 1)) A)ˣ :=
  Units.map (expandMatrixHom F hp)

theorem expandUnits_compressUnits (hp : 0 < p) (X : (Matrix (Fin (p + 1)) (Fin (p + 1)) A)ˣ) :
    expandUnits F hp (compressUnits F hp X) = X :=
  Units.ext (expand_compress F hp (X : Matrix (Fin (p + 1)) (Fin (p + 1)) A))

end Units

section Leavitt

variable (k : Type) [Field k]

theorem steinbergToGL_x {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a : BinaryLeavitt.BinaryLeavittAlgebra k) :
    LVEGen.steinbergToGL k n (x i j hij a) = elementaryUnit i j hij a := by
  change ((projection (x i j hij a) :
      elementaryGroup (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
        (Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ) =
    elementaryUnit i j hij a
  rw [projection_x, elementaryRoot_val]

variable {p : ℕ}

/-- **Generator identity.** `δ ∘ π_{p+1} ∘ pad = π_p ∘ κ̃` on `St_p(L)`. -/
theorem compressUnits_steinbergToGL_indexMap (hp : 0 < p)
    (y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
    compressUnits (BinaryLeavitt.family k) hp
        (LVEGen.steinbergToGL k (p + 1) (indexMap (Fin.castLEEmb (Nat.le_succ p)) y)) =
      LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p y) := by
  have hh : (compressUnits (BinaryLeavitt.family k) hp).comp
      ((LVEGen.steinbergToGL k (p + 1)).comp (indexMap (Fin.castLEEmb (Nat.le_succ p)))) =
      (LVEGen.steinbergToGL k p).comp (steinbergCompress (BinaryLeavitt.family k) p) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change compressUnits (BinaryLeavitt.family k) hp
        (LVEGen.steinbergToGL k (p + 1) (indexMap (Fin.castLEEmb (Nat.le_succ p)) (x i j hij a))) =
      LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p (x i j hij a))
    rw [indexMap_x, steinbergCompress_x, steinbergToGL_x, steinbergToGL_x]
    refine Units.ext ?_
    exact compressMatrixHom_one_add_single (BinaryLeavitt.family k) hp i j a
  exact DFunLike.congr_fun hh y

/-- `κ̃` maps `K₂(p, L)` into `ker (St_p(L) → GL_p(L))`. -/
theorem steinbergToGL_steinbergCompress_eq_one (hp : 0 < p)
    {y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)} (hy : projection y = 1) :
    LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p y) = 1 := by
  rw [← compressUnits_steinbergToGL_indexMap k hp y]
  have h1 : projection (indexMap (Fin.castLEEmb (Nat.le_succ p)) y) = 1 :=
    LVH2GL3.projection_indexMap_eq_one _ hy
  change compressUnits (BinaryLeavitt.family k) hp
      ((projection (indexMap (Fin.castLEEmb (Nat.le_succ p)) y) :
        elementaryGroup (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
          (Matrix (Fin (p + 1)) (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ) = 1
  rw [h1]
  exact map_one (compressUnits (BinaryLeavitt.family k) hp)

/-- `κ̃` maps `K₂(p, L)` into itself. -/
theorem projection_steinbergCompress_eq_one (hp : 0 < p)
    {y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)} (hy : projection y = 1) :
    projection (steinbergCompress (BinaryLeavitt.family k) p y) = 1 :=
  Subtype.ext (steinbergToGL_steinbergCompress_eq_one k hp hy)

/-- **Idempotence up to conjugation.** `π_p ∘ κ̃ ∘ κ̃ = Ad(g) ∘ π_p ∘ κ̃` with
`g = diag(w, 1, …, 1)` (Khanh, arXiv:2609.08428, proof of Prop. 3.2). -/
theorem steinbergToGL_steinbergCompress_steinbergCompress
    (y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
    LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p
        (steinbergCompress (BinaryLeavitt.family k) p y)) =
      diagMatrixUnit (coordConjUnit (BinaryLeavitt.family k)) *
          LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p y) *
        (diagMatrixUnit (coordConjUnit (BinaryLeavitt.family k)))⁻¹ := by
  have hh : (LVEGen.steinbergToGL k p).comp ((steinbergCompress (BinaryLeavitt.family k) p).comp
      (steinbergCompress (BinaryLeavitt.family k) p)) =
      (MulAut.conj (diagMatrixUnit (coordConjUnit (BinaryLeavitt.family k)))).toMonoidHom.comp
        ((LVEGen.steinbergToGL k p).comp (steinbergCompress (BinaryLeavitt.family k) p)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p
        (steinbergCompress (BinaryLeavitt.family k) p (x i j hij a))) =
      MulAut.conj (diagMatrixUnit (coordConjUnit (BinaryLeavitt.family k)))
        (LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p (x i j hij a)))
    simp only [steinbergCompress_x, steinbergToGL_x, MulAut.conj_apply]
    rw [diagMatrixUnit_mul_elementaryUnit_mul_inv, coordConj_scalar]
  exact DFunLike.congr_fun hh y

end Leavitt

end LVStability
end Full
end GroupApproximation
