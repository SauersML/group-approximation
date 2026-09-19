import GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainVertex
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Develop
import GroupApproximation.Meta.AxiomGuard

/-!
# Z.3, part 3: types along edges, the standard chamber, and the `TriangleAction` reduction

Lane `fix-bh-a`, piece Z.3 (board `k2-poly.md`).  The target shape is bh-pal-linear-char0's
`TriangleAction` (`BTri/Develop.lean`), which Z.5/Z.6 consume.

* `detVal_eq_add`: if `h = g K` with `det K = p^d u`, then `detVal h = detVal g + d`.
* `exists_detVal_of_incident`: if `p L < L' < L` (column lattices of `g` and `h`), then
  `detVal h = detVal g + d` with `d ∈ {1, 2}`.  Write `L' = g K A³` and `pL = h K' A³`; then
  `det K · det K' = p³`, so `det K ~ p^d`.  If `d = 0` then `L' = L`, and if `d = 3` then
  `L' = pL`.
* **`vertexType_adj`**: adjacent vertices have different types.
* **`std_adj`**: the three standard vertices are pairwise adjacent (the standard chamber).
* `vertexIndex hp = stdOfType ∘ vertexType hp : Vertex → Fin 3`, the type as used by
  `TriangleAction`.
* `EdgeNormalForm A p` and `ChamberNormalForm A p`: the `edge` and `chamber` fields of
  `TriangleAction` for this action, as named Props.  They are discharged in `DomainChamber.lean`.
* **`triangleAction_sl3_of`**: `EdgeNormalForm A p → ChamberNormalForm A p →
  TriangleAction SL₃(A[1/p]) (buildingGraph …) (stdVertex A p) (vertexIndex hp)`.  The other five
  fields are proved here.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped Pointwise
open Matrix

section Incident

variable {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [Algebra A B]
  {p : A} [IsLocalization.Away p B]

/-- If `h = g K` with `det K = p^d u`, then `detVal h = detVal g + d`. -/
theorem detVal_eq_add (hp : Prime p) {g h : GL (Fin 3) B} {K : Matrix (Fin 3) (Fin 3) A}
    (e : (h : Matrix (Fin 3) (Fin 3) B) = (g : Matrix (Fin 3) (Fin 3) B) * K.map (algebraMap A B))
    {u : Aˣ} {d : ℕ} (hK : K.det = p ^ d * u) : detVal hp h = detVal hp g + d := by
  have hdet : Matrix.GeneralLinearGroup.det h =
      Matrix.GeneralLinearGroup.det g * (unitsMap u * pU (B := B) p ^ d) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_unitsMap, coe_pU]
    change Matrix.det (h : Matrix (Fin 3) (Fin 3) B) =
      Matrix.det (g : Matrix (Fin 3) (Fin 3) B) * (algebraMap A B u * algebraMap A B p ^ d)
    rw [e, Matrix.det_mul,
      show Matrix.det (K.map (algebraMap A B)) = algebraMap A B K.det from
        (RingHom.map_det _ _).symm, hK, map_mul, map_pow]
    ring
  unfold detVal
  rw [hdet, pval_mul, pval_mul, pval_map, ← zpow_natCast, pval_pU_pow, zero_add]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_eq_add

/-- The lattice `p • latOf g` is the lattice of `p g`. -/
theorem smul_latOf_one (g : GL (Fin 3) B) :
    p • latOf A B g =
      latOf A B (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p) * g) := by
  have h := smul_latOf (A := A) (B := B) p 1 g
  simp only [pow_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.smul_latOf_one

theorem detVal_scalar_mul (hp : Prime p) (g : GL (Fin 3) B) :
    detVal hp (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p) * g) = 3 + detVal hp g := by
  rw [detVal_mul]
  have := detVal_scalar (A := A) (B := B) hp 1
  simp only [pow_one, Nat.cast_one, mul_one] at this
  rw [this]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_scalar_mul

/-- A matrix over `A` with unit determinant, as an element of `GL₃(A)`. -/
noncomputable def glOfIsUnit (K : Matrix (Fin 3) (Fin 3) A) (h : IsUnit K.det) : GL (Fin 3) A :=
  Matrix.GeneralLinearGroup.mk'' K h

theorem latOf_eq_of_eq_mul_isUnit {g h : GL (Fin 3) B} {K : Matrix (Fin 3) (Fin 3) A}
    (e : (h : Matrix (Fin 3) (Fin 3) B) = (g : Matrix (Fin 3) (Fin 3) B) * K.map (algebraMap A B))
    (hK : IsUnit K.det) : latOf A B h = latOf A B g := by
  have : h = g * Matrix.GeneralLinearGroup.map (algebraMap A B) (glOfIsUnit K hK) :=
    Matrix.GeneralLinearGroup.ext fun i j => by rw [e]; rfl
  rw [this, latOf_mul_map]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.latOf_eq_of_eq_mul_isUnit

/-- **Types along an incidence**: `p L < L' < L` gives `detVal h = detVal g + d`, `d ∈ {1, 2}`. -/
theorem exists_detVal_of_incident (hp : Prime p) {g h : GL (Fin 3) B}
    (h1 : p • latOf A B g < latOf A B h) (h2 : latOf A B h < latOf A B g) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ detVal hp h = detVal hp g + d := by
  obtain ⟨K, hK⟩ := exists_eq_mul_of_latOf_le h2.le
  rw [smul_latOf_one] at h1
  obtain ⟨K', hK'⟩ := exists_eq_mul_of_latOf_le h1.le
  have hdet : K.det * K'.det = p ^ 3 := by
    apply algebraMap_injective (B := B) hp
    have e1 : (g : Matrix (Fin 3) (Fin 3) B) * (K.map (algebraMap A B) * K'.map (algebraMap A B)) =
        Matrix.scalar (Fin 3) (algebraMap A B p) * (g : Matrix (Fin 3) (Fin 3) B) := by
      rw [← mul_assoc, ← hK, ← hK', Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, coe_pU]
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      show Matrix.det (K.map (algebraMap A B)) = algebraMap A B K.det from (RingHom.map_det _ _).symm,
      show Matrix.det (K'.map (algebraMap A B)) = algebraMap A B K'.det from (RingHom.map_det _ _).symm,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_comm _ (Matrix.det _)] at e2
    have hu : IsUnit (Matrix.det (g : Matrix (Fin 3) (Fin 3) B)) :=
      (Matrix.GeneralLinearGroup.det g).isUnit
    rw [map_mul, map_pow]
    exact hu.mul_left_cancel e2
  obtain ⟨d, hd3, w, hw⟩ := (dvd_prime_pow hp 3).mp ⟨K'.det, hdet.symm⟩
  have hKd : K.det = p ^ d * ((w⁻¹ : Aˣ) : A) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨d, ?_, detVal_eq_add hp hK hKd⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    have hu : IsUnit K.det := by
      rw [hKd, pow_zero, one_mul]
      exact Units.isUnit _
    exact h2.ne (latOf_eq_of_eq_mul_isUnit hK hu)
  have hd3' : d ≠ 3 := by
    rintro rfl
    have hK0 : K.det ≠ 0 := by
      rw [hKd]
      exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Units.ne_zero _)
    have hw' : K'.det = w := by
      apply mul_left_cancel₀ hK0
      rw [hdet, hw]
    have hu : IsUnit K'.det := by
      rw [hw']
      exact Units.isUnit _
    exact h1.ne (latOf_eq_of_eq_mul_isUnit hK' hu)
  omega

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_detVal_of_incident

theorem vertexType_ne_of_incident (hp : Prime p) {x y : Vertex A B p} (h : Incident A B p x y) :
    vertexType hp x ≠ vertexType hp y := by
  obtain ⟨g, g', rfl, rfl, h1, h2⟩ := h
  obtain ⟨d, hd, e⟩ := exists_detVal_of_incident hp h1 h2
  rw [vertexType_vertexOf, vertexType_vertexOf, e]
  push_cast
  intro H
  have h0 : ((d : ℕ) : ZMod 3) = 0 := by linear_combination -H
  rcases hd with rfl | rfl <;> exact absurd h0 (by decide)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_ne_of_incident

/-- **Adjacent vertices have different types.** -/
theorem vertexType_adj (hp : Prime p) {x y : Vertex A B p} (h : (buildingGraph A B p).Adj x y) :
    vertexType hp x ≠ vertexType hp y := by
  obtain ⟨-, h | h⟩ := h
  · exact vertexType_ne_of_incident hp h
  · exact (vertexType_ne_of_incident hp h).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_adj

/-- An incidence from explicit matrices, with strictness certified by `detVal`. -/
theorem incident_of_mul (hp : Prime p) {g h : GL (Fin 3) B} {K K' : Matrix (Fin 3) (Fin 3) A}
    (e : (h : Matrix (Fin 3) (Fin 3) B) = (g : Matrix (Fin 3) (Fin 3) B) * K.map (algebraMap A B))
    (e' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p) * g : GL (Fin 3) B) :
        Matrix (Fin 3) (Fin 3) B) = (h : Matrix (Fin 3) (Fin 3) B) * K'.map (algebraMap A B))
    (hne : detVal hp h ≠ detVal hp g) (hne' : detVal hp h ≠ 3 + detVal hp g) :
    Incident A B p (vertexOf A B p g) (vertexOf A B p h) := by
  refine ⟨g, h, rfl, rfl, ?_, ?_⟩
  · rw [smul_latOf_one]
    refine lt_of_le_of_ne (latOf_le_of_eq_mul e') fun eq => hne' ?_
    obtain ⟨k, hk⟩ := exists_eq_mul_map_of_latOf_eq p hp eq
    rw [hk, detVal_mul, detVal_map, add_zero, detVal_scalar_mul]
  · refine lt_of_le_of_ne (latOf_le_of_eq_mul e) fun eq => hne ?_
    obtain ⟨k, hk⟩ := exists_eq_mul_map_of_latOf_eq p hp eq.symm
    rw [hk, detVal_mul, detVal_map, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.incident_of_mul

end Incident

section Std

variable {A : Type*} [CommRing A] [IsDomain A] {p : A}

theorem diag_pow_eq_mul (e e' : Fin 3 → ℕ) (h : ∀ k, e k ≤ e' k) :
    (diagonal fun k => algebraMap A (Localization.Away p) p ^ e' k :
        Matrix (Fin 3) (Fin 3) (Localization.Away p)) =
      (diagonal fun k => algebraMap A (Localization.Away p) p ^ e k) *
        (diagonal fun k => p ^ (e' k - e k)).map (algebraMap A (Localization.Away p)) := by
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  rw [map_pow, ← pow_add, Nat.add_sub_cancel' (h k)]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.diag_pow_eq_mul

theorem coe_scalar_stdMat (i : Fin 3) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := Localization.Away p) p) * stdMat A p i :
        GL (Fin 3) (Localization.Away p)) : Matrix (Fin 3) (Fin 3) (Localization.Away p)) =
      diagonal fun k => algebraMap A (Localization.Away p) p ^ (stdExp i k + 1) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_pU, coe_stdMat,
    Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  rw [pow_succ, mul_comm]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.coe_scalar_stdMat

theorem stdExp_mono : ∀ i j : Fin 3, i < j → ∀ k, stdExp i k ≤ stdExp j k := by
  decide

theorem stdExp_le_succ : ∀ i j : Fin 3, i < j → ∀ k, stdExp j k ≤ stdExp i k + 1 := by
  decide

/-- The standard vertices `i < j` are incident: `p L_i < L_j < L_i`. -/
theorem incident_std (hp : Prime p) {i j : Fin 3} (hij : i < j) :
    Incident A (Localization.Away p) p (stdVertex A p i) (stdVertex A p j) := by
  unfold stdVertex
  refine incident_of_mul hp (K := diagonal fun k => p ^ (stdExp j k - stdExp i k))
    (K' := diagonal fun k => p ^ (stdExp i k + 1 - stdExp j k)) ?_ ?_ ?_ ?_
  · rw [coe_stdMat, coe_stdMat]
    exact diag_pow_eq_mul _ _ (stdExp_mono i j hij)
  · rw [coe_scalar_stdMat, coe_stdMat]
    exact diag_pow_eq_mul (fun k => stdExp j k) (fun k => stdExp i k + 1) (stdExp_le_succ i j hij)
  · rw [detVal_stdMat, detVal_stdMat]
    exact_mod_cast (Fin.val_lt_of_lt hij).ne'
  · rw [detVal_stdMat, detVal_stdMat]
    have := j.isLt
    omega

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.incident_std

/-- **The standard chamber**: the standard vertices are pairwise adjacent. -/
theorem std_adj (hp : Prime p) {i j : Fin 3} (hij : i ≠ j) :
    (buildingGraph A (Localization.Away p) p).Adj (stdVertex A p i) (stdVertex A p j) := by
  refine ⟨fun e => hij ?_, ?_⟩
  · have := congrArg (vertexType hp) e
    rw [vertexType_std, vertexType_std] at this
    calc i = stdOfType (i.val : ZMod 3) := (stdOfType_natCast i).symm
      _ = stdOfType (j.val : ZMod 3) := by rw [this]
      _ = j := stdOfType_natCast j
  · rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (incident_std hp h)
    · exact Or.inr (incident_std hp h)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.std_adj

/-- The type of a vertex as an element of `Fin 3` (the `τ` of `TriangleAction`). -/
noncomputable def vertexIndex (hp : Prime p) (x : Vertex A (Localization.Away p) p) : Fin 3 :=
  stdOfType (vertexType hp x)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexIndex

theorem stdOfType_injective : Function.Injective stdOfType := by
  intro s t h
  exact ZMod.val_injective 3 (congrArg Fin.val h)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.stdOfType_injective

theorem vertexIndex_std (hp : Prime p) (i : Fin 3) : vertexIndex hp (stdVertex A p i) = i := by
  rw [vertexIndex, vertexType_std, stdOfType_natCast]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexIndex_std

variable (A p) in
/-- The `edge` field of `TriangleAction`: an edge can be moved onto the standard edge of the
same types. -/
def EdgeNormalForm (hp : Prime p) : Prop :=
  ∀ x y : Vertex A (Localization.Away p) p, (buildingGraph A (Localization.Away p) p).Adj x y →
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p),
      g • x = stdVertex A p (vertexIndex hp x) ∧ g • y = stdVertex A p (vertexIndex hp y)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.EdgeNormalForm

variable (A p) in
/-- The `chamber` field of `TriangleAction`: a triangle can be moved onto the standard chamber,
preserving types. -/
def ChamberNormalForm (hp : Prime p) : Prop :=
  ∀ x y z : Vertex A (Localization.Away p) p, (buildingGraph A (Localization.Away p) p).Adj x y →
    (buildingGraph A (Localization.Away p) p).Adj y z →
      (buildingGraph A (Localization.Away p) p).Adj x z →
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p),
      g • x = stdVertex A p (vertexIndex hp x) ∧ g • y = stdVertex A p (vertexIndex hp y) ∧
        g • z = stdVertex A p (vertexIndex hp z)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.ChamberNormalForm

variable (A p) in
/-- **The `SL₃(A[1/p])`-action on the building, as a `TriangleAction`**, from the edge and
chamber normal forms. -/
theorem triangleAction_sl3_of (hp : Prime p) (hE : EdgeNormalForm A p hp)
    (hC : ChamberNormalForm A p hp) :
    TriangleAction (Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p))
      (buildingGraph A (Localization.Away p) p) (stdVertex A p) (vertexIndex hp) where
  adj_smul g x y := by
    rw [sl_smul_def, sl_smul_def]
    exact buildingGraph_adj_smul A (Localization.Away p) p _ x y
  type_smul g x := by
    rw [vertexIndex, vertexIndex, vertexType_sl_smul]
  type_std i := vertexIndex_std hp i
  type_adj x y h := fun e => vertexType_adj hp h (stdOfType_injective e)
  std_adj i j hij := std_adj hp hij
  edge := hE
  chamber := hC

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.triangleAction_sl3_of

end Std

end BTri
end BooneHigmanLinear
end GroupApproximation
