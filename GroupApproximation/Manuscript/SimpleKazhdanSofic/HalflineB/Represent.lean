import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Tables
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeInvariant
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): every element of `R_Δ` is a table, and words multiply out

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b), tex l.657–664 (sentences 7bfa078c0bed and
e3cd35e16e2f):

> A word in the generators of G_Δ multiplies out to a matrix with entries Σ_ξ p_ξ u_ξ, where each p_ξ is a
> polynomial over F_2 in finitely many coordinates x(δ), as u_ξ e_U u_ξ^{-1} is the indicator of
> {x : x(δ) = 1 + c(δ)} for ξ : x ↦ δx + c. After collecting equal ξ and equal coordinates, the word is trivial if
> and only if every coefficient of its difference from I_3 vanishes at every assignment of its finitely many
> variables, as Ω is the full shift.

## Proof route

* `liftD v` is the word `v` in the letters `t i` of `Λ`; its atom is the coordinate `x ↦ x(value v)`
  (`hAtom_liftD`, from `comap_smulMap_inr_inv_coord`).
* The finite sums of atom products form a subring of `LC(Ω, F₂)` (`cylSubring`, using `-f = f` in characteristic
  two). It contains the coordinates, which generate (`closure_range_coord`), so every `f` is such a sum
  (`exists_cylList_eq`).
* Every `r ∈ R_Δ` is `Σ_{ξ ∈ S} f_ξ u_ξ` (`exists_sum_coeff_mul_unit`); with a word for each `ξ` and a cylinder list
  for each `f_ξ`, `r` is the value of a table (`exists_hTab_eq`), and matrices are matrices of tables
  (`exists_hMat_eq`).
* A word in finitely many units `v` of `M₃(R_Δ)`, with a table matrix `L x` for each letter, multiplies out to the
  table matrix `hWordMat L w` (`hMatEval_hWordMat`, by `hMatEval_hMatMul`). It is trivial iff every entry of
  `hWordMat L w + I₃` vanishes, in characteristic two (`wordValue_eq_one_iff_hTab`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter
open SkewMonoidAlgebra (single)

variable {Δ : Type} [Group Δ] {ι : Type}

/-! ### Words in `Δ` as words in `Λ` -/

/-- A word in the `t i` as a word in the generators of `Λ`. -/
def liftD : List (ι × Bool) → LW ι
  | [] => []
  | (i, b) :: v => (some i, b) :: liftD v

theorem lampPrefixes_liftD (v : List (ι × Bool)) : lampPrefixes (liftD v) = [] := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    obtain ⟨i, b⟩ := x
    simp only [liftD, lampPrefixes, ih, List.map_nil]

theorem deltaWord_liftD (v : List (ι × Bool)) : deltaWord (liftD v) = v := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    obtain ⟨i, b⟩ := x
    simp only [liftD, deltaWord, ih]

theorem wordValue_lampGen_liftD (s : ι → Δ) (v : List (ι × Bool)) :
    wordValue (lampGen s) (liftD v) = SemidirectProduct.inr (wordValue s v) := by
  rw [wordValue_lampGen, deltaWord_liftD, lampSum, lampPrefixes_liftD, List.map_nil, List.sum_nil, ofAdd_zero,
    map_one, one_mul]

/-- The atom of a word in `Δ` is the coordinate at its value. -/
theorem hAtom_liftD (s : ι → Δ) (v : List (ι × Bool)) : hAtom s (liftD v) = coord Δ (wordValue s v) := by
  rw [hAtom, wordValue_lampGen_liftD, comap_smulMap_inr_inv_coord]

/-! ### Every locally constant function is a sum of atom products -/

theorem cylSum_map_append (s : ι → Δ) (P : List (LW ι)) (L : List (List (LW ι))) :
    ((L.map (P ++ ·)).map (hCyl s)).sum = hCyl s P * (L.map (hCyl s)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons Q L ih => simp only [List.map_cons, List.sum_cons, ih, hCyl_append, mul_add]

theorem cylSum_flatMap (s : ι → Δ) (L L' : List (List (LW ι))) :
    ((L.flatMap fun P => L'.map (P ++ ·)).map (hCyl s)).sum =
      (L.map (hCyl s)).sum * (L'.map (hCyl s)).sum := by
  induction L with
  | nil => simp only [List.flatMap_nil, List.map_nil, List.sum_nil, zero_mul]
  | cons P L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, cylSum_map_append, ih, List.map_cons,
      List.sum_cons, add_mul]

/-- The finite sums of atom products. -/
noncomputable def cylSubring (s : ι → Δ) : Subring (LocallyConstant (LampSpace Δ) (ZMod 2)) where
  carrier := {f | ∃ L : List (List (LW ι)), (L.map (hCyl s)).sum = f}
  zero_mem' := ⟨[], by rw [List.map_nil, List.sum_nil]⟩
  one_mem' := ⟨[[]], by rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hCyl]⟩
  add_mem' := by
    rintro _ _ ⟨L, rfl⟩ ⟨L', rfl⟩
    exact ⟨L ++ L', by rw [List.map_append, List.sum_append]⟩
  mul_mem' := by
    rintro _ _ ⟨L, rfl⟩ ⟨L', rfl⟩
    exact ⟨L.flatMap fun P => L'.map (P ++ ·), cylSum_flatMap s L L'⟩
  neg_mem' := by
    rintro _ ⟨L, rfl⟩
    refine ⟨L, LocallyConstant.ext fun x => ?_⟩
    rw [LocallyConstant.neg_apply, ZMod.neg_eq_self_mod_two]

theorem exists_cylList_eq (s : ι → Δ) (hs : Subgroup.closure (Set.range s) = ⊤)
    (f : LocallyConstant (LampSpace Δ) (ZMod 2)) : ∃ L : List (List (LW ι)), (L.map (hCyl s)).sum = f := by
  have hle : Subring.closure (Set.range (coord Δ)) ≤ cylSubring s := by
    refine Subring.closure_le.2 ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨v, hv⟩ := exists_wordValue_eq hs h
    show ∃ L : List (List (LW ι)), (L.map (hCyl s)).sum = coord Δ h
    refine ⟨[[liftD v]], ?_⟩
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hCyl, hCyl, mul_one, hAtom_liftD,
      hv]
  have hf : f ∈ Subring.closure (Set.range (coord Δ)) := by
    rw [closure_range_coord Δ]
    exact Subring.mem_top f
  exact hle hf

/-! ### Every element of `R_Δ` is a table -/

theorem closure_range_lampGen (s : ι → Δ) (hs : Subgroup.closure (Set.range s) = ⊤) :
    Subgroup.closure (Set.range (lampGen s)) = ⊤ := by
  have hrange : Set.range (lampGen s) =
      insert (lampAdd Δ) ((SemidirectProduct.inr : Δ →* LampAffine Δ) '' Set.range s) := by
    ext ξ
    constructor
    · rintro ⟨(_ | i), rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨s i, ⟨i, rfl⟩, rfl⟩
    · rintro (rfl | ⟨_, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
  rw [hrange]
  exact closure_insert_lampAdd_image_inr Δ hs

theorem hTabEval_map_pair (s : ι → Δ) (a : LW ι) (L : List (List (LW ι))) :
    hTabEval s (L.map fun P => (a, P)) =
      single (wordValue (lampGen s) a)
        (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (L.map (hCyl s)).sum) := by
  induction L with
  | nil => simp only [List.map_nil, hTabEval_nil, List.sum_nil, map_zero, SkewMonoidAlgebra.single_zero]
  | cons P L ih =>
    simp only [List.map_cons, hTabEval_cons, ih, List.sum_cons, map_add, SkewMonoidAlgebra.single_add, hMonoEval]

theorem hTabEval_flatMap {α : Type*} (s : ι → Δ) (L : List α) (g : α → HTable ι) :
    hTabEval s (L.flatMap g) = (L.map fun x => hTabEval s (g x)).sum := by
  induction L with
  | nil => simp only [List.flatMap_nil, hTabEval_nil, List.map_nil, List.sum_nil]
  | cons x L ih => simp only [List.flatMap_cons, hTabEval_append, ih, List.map_cons, List.sum_cons]

/-- **Every element of `R_Δ` is the value of a table** `Σ_ξ p_ξ u_ξ`. -/
theorem exists_hTab_eq (s : ι → Δ) (hs : Subgroup.closure (Set.range s) = ⊤) (r : LampRing Δ) :
    ∃ T : HTable ι, hTabEval s T = r := by
  obtain ⟨S, f, rfl⟩ :=
    ClopenGroupCrossedProduct.exists_sum_coeff_mul_unit (LampAffine Δ) (LampSpace Δ) (ZMod 2) r
  choose a ha using fun ξ : LampAffine Δ => exists_wordValue_eq (closure_range_lampGen s hs) ξ
  choose L hL using fun ξ : LampAffine Δ => exists_cylList_eq s hs (f ξ)
  refine ⟨S.toList.flatMap fun ξ => (L ξ).map fun P => (a ξ, P), ?_⟩
  rw [hTabEval_flatMap, ← Finset.sum_map_toList]
  congr 1
  refine List.map_congr_left fun ξ _ => ?_
  dsimp only
  rw [hTabEval_map_pair, ha, hL, ClopenGroupCrossedProduct.single_eq_coeff_mul_unit]

theorem exists_hMat_eq (s : ι → Δ) (hs : Subgroup.closure (Set.range s) = ⊤)
    (A : Matrix (Fin 3) (Fin 3) (LampRing Δ)) : ∃ M : HMat ι, hMatEval s M = A := by
  choose M hM using fun i j => exists_hTab_eq s hs (A i j)
  exact ⟨M, Matrix.ext fun i j => (hMatEval_apply s M i j).trans (hM i j)⟩

/-! ### Words multiply out -/

/-- The table matrix of a word, from table matrices `L x` of its letters. -/
def hWordMat {κ : Type} (L : κ × Bool → HMat ι) (w : List (κ × Bool)) : HMat ι :=
  w.foldr (fun x M => hMatMul (L x) M) hMatOne

theorem hWordMat_nil {κ : Type} (L : κ × Bool → HMat ι) : hWordMat L [] = hMatOne :=
  rfl

theorem hWordMat_cons {κ : Type} (L : κ × Bool → HMat ι) (x : κ × Bool) (w : List (κ × Bool)) :
    hWordMat L (x :: w) = hMatMul (L x) (hWordMat L w) :=
  rfl

/-- **A word multiplies out to its table matrix** (tex l.657–658). -/
theorem hMatEval_hWordMat (s : ι → Δ) {κ : Type} (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ)
    (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval s (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ)))
    (w : List (κ × Bool)) :
    hMatEval s (hWordMat L w) = ((wordValue v w : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
      Matrix (Fin 3) (Fin 3) (LampRing Δ)) := by
  induction w with
  | nil => rw [hWordMat_nil, hMatEval_hMatOne, wordValue_nil, Units.val_one]
  | cons x w ih => rw [hWordMat_cons, hMatEval_hMatMul, hL, ih, wordValue_cons, Units.val_mul]

/-- **The triviality criterion** (tex l.661–664): a word in the units `v` is trivial iff every entry of its table
matrix plus `I₃` (its difference from `I₃`, in characteristic two) is the zero table. -/
theorem wordValue_eq_one_iff_hTab (s : ι → Δ) {κ : Type} (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ)
    (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval s (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ)))
    (w : List (κ × Bool)) :
    wordValue v w = 1 ↔ ∀ i j : Fin 3, hTabEval s (hWordMat L w i j ++ hMatOne i j) = 0 := by
  rw [← Units.val_eq_one, ← hMatEval_hWordMat s v L hL w, ← hMatEval_hMatOne s]
  constructor
  · intro h i j
    rw [hTabEval_append, ← lampRing_eq_iff_add_eq_zero]
    exact congrFun (congrFun h i) j
  · intro h
    refine Matrix.ext fun i j => ?_
    rw [hMatEval_apply, hMatEval_apply, lampRing_eq_iff_add_eq_zero, ← hTabEval_append]
    exact h i j

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.exists_hMat_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.wordValue_eq_one_iff_hTab
