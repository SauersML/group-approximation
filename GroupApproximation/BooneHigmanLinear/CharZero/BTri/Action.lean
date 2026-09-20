import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Building
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Diagonal
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL₃(B)` acts on the lattice building (Z1-base, piece Z.2)

* `latOf_mul`: `latOf (γ g)` is the image of `latOf g` under `v ↦ γ v`.
* `instance : MulAction (GL (Fin 3) B) (Vertex A B p)`, `smul_vertexOf`.
* `buildingGraph_adj_smul`: each `γ` is a graph automorphism of `buildingGraph`.
* `SL₃(B)` acts through `Matrix.SpecialLinearGroup.toGL`.
* The standard chamber, for `B = A[1/p]`: `stdMat 0 = 1`, `stdMat 1 = diag(1,1,p)`,
  `stdMat 2 = diag(1,p,p)`, and `stdVertex i = vertexOf (stdMat i)`.

The classification of vertices, edges and chambers up to `SL₃(B)` is piece Z.3 (lane fix-bh-a,
`BTri/Domain*.lean`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped Pointwise

section Action

variable (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B] (p : A)

/-- Left multiplication by `γ`, as an `A`-linear map of `B³`. -/
def glLin (γ : Matrix.GeneralLinearGroup (Fin 3) B) : (Fin 3 → B) →ₗ[A] (Fin 3 → B) :=
  (Matrix.mulVecLin (γ : Matrix (Fin 3) (Fin 3) B)).restrictScalars A

theorem glLin_injective (γ : Matrix.GeneralLinearGroup (Fin 3) B) :
    Function.Injective (glLin A B γ) := by
  intro v w h
  have h' := congrArg (fun u => Matrix.mulVec ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) B) :
    Matrix (Fin 3) (Fin 3) B) u) h
  simp only [glLin, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h'
  exact h'

#audit_axioms glLin_injective

theorem latOf_mul (γ g : Matrix.GeneralLinearGroup (Fin 3) B) :
    latOf A B (γ * g) = (latOf A B g).map (glLin A B γ) := by
  rw [latOf, latOf, Submodule.map_span, ← Set.range_comp]
  rfl

#audit_axioms latOf_mul

variable {A} in
/-- Pointwise scaling commutes with linear images. -/
theorem map_pointwise_smul_lat (c : A) (L : Submodule A (Fin 3 → B))
    (f : (Fin 3 → B) →ₗ[A] (Fin 3 → B)) : (c • L).map f = c • L.map f := by
  ext v
  simp only [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, (map_smul f c u).symm⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨c • u, ⟨u, hu, rfl⟩, map_smul f c u⟩

#audit_axioms map_pointwise_smul_lat

theorem homothetic_mul (γ : Matrix.GeneralLinearGroup (Fin 3) B)
    {g h : Matrix.GeneralLinearGroup (Fin 3) B} (hgh : Homothetic A B p g h) :
    Homothetic A B p (γ * g) (γ * h) := by
  obtain ⟨a, b, hab⟩ := hgh
  exact ⟨a, b, by
    rw [latOf_mul, latOf_mul, ← map_pointwise_smul_lat, ← map_pointwise_smul_lat, hab]⟩

#audit_axioms homothetic_mul

/-- **`GL₃(B)` acts on the vertices by left multiplication.** -/
instance instMulActionVertex : MulAction (Matrix.GeneralLinearGroup (Fin 3) B) (Vertex A B p) where
  smul γ := Quotient.map (γ * ·) fun _ _ hgh => homothetic_mul A B p γ hgh
  one_smul x := Quotient.inductionOn x fun g => by
    change vertexOf A B p (1 * g) = vertexOf A B p g
    rw [one_mul]
  mul_smul γ δ x := Quotient.inductionOn x fun g => by
    change vertexOf A B p (γ * δ * g) = vertexOf A B p (γ * (δ * g))
    rw [mul_assoc]

theorem smul_vertexOf (γ g : Matrix.GeneralLinearGroup (Fin 3) B) :
    γ • vertexOf A B p g = vertexOf A B p (γ * g) :=
  rfl

theorem latOf_lt_mul (γ : Matrix.GeneralLinearGroup (Fin 3) B)
    {g h : Matrix.GeneralLinearGroup (Fin 3) B} (hlt : latOf A B g < latOf A B h) :
    latOf A B (γ * g) < latOf A B (γ * h) := by
  rw [latOf_mul, latOf_mul]
  exact Submodule.map_strictMono_of_injective (glLin_injective A B γ) hlt

#audit_axioms latOf_lt_mul

theorem smul_latOf_lt_mul (γ : Matrix.GeneralLinearGroup (Fin 3) B)
    {g h : Matrix.GeneralLinearGroup (Fin 3) B} (hlt : p • latOf A B g < latOf A B h) :
    p • latOf A B (γ * g) < latOf A B (γ * h) := by
  rw [latOf_mul, latOf_mul, ← map_pointwise_smul_lat]
  exact Submodule.map_strictMono_of_injective (glLin_injective A B γ) hlt

#audit_axioms smul_latOf_lt_mul

theorem incident_smul (γ : Matrix.GeneralLinearGroup (Fin 3) B) {x y : Vertex A B p}
    (hxy : Incident A B p x y) : Incident A B p (γ • x) (γ • y) := by
  obtain ⟨g, h, rfl, rfl, h₁, h₂⟩ := hxy
  exact ⟨γ * g, γ * h, rfl, rfl, smul_latOf_lt_mul A B p γ h₁, latOf_lt_mul A B γ h₂⟩

#audit_axioms incident_smul

theorem adj_smul_of_adj (γ : Matrix.GeneralLinearGroup (Fin 3) B) {x y : Vertex A B p}
    (hxy : (buildingGraph A B p).Adj x y) : (buildingGraph A B p).Adj (γ • x) (γ • y) := by
  rw [buildingGraph, SimpleGraph.fromRel_adj] at hxy ⊢
  obtain ⟨hne, h⟩ := hxy
  refine ⟨fun heq => hne (smul_left_cancel γ heq), ?_⟩
  rcases h with h | h
  · exact Or.inl (incident_smul A B p γ h)
  · exact Or.inr (incident_smul A B p γ h)

#audit_axioms adj_smul_of_adj

/-- **Every `γ ∈ GL₃(B)` is a graph automorphism of the building.** -/
theorem buildingGraph_adj_smul (γ : Matrix.GeneralLinearGroup (Fin 3) B) (x y : Vertex A B p) :
    (buildingGraph A B p).Adj (γ • x) (γ • y) ↔ (buildingGraph A B p).Adj x y := by
  refine ⟨fun h => ?_, adj_smul_of_adj A B p γ⟩
  have h' := adj_smul_of_adj A B p γ⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at h'

#audit_axioms buildingGraph_adj_smul

/-- `SL₃(B)` acts through `toGL`. -/
instance instMulActionVertexSL : MulAction (Matrix.SpecialLinearGroup (Fin 3) B) (Vertex A B p) :=
  MulAction.compHom _ Matrix.SpecialLinearGroup.toGL

theorem sl_smul_def (γ : Matrix.SpecialLinearGroup (Fin 3) B) (x : Vertex A B p) :
    γ • x = (Matrix.SpecialLinearGroup.toGL γ) • x :=
  rfl

end Action

section Standard

variable (A : Type*) [CommRing A] (p : A)

/-- `p` as a unit of `A[1/p]`. -/
noncomputable def pUnit : (Localization.Away p)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit p).unit

/-- The standard chamber matrices: `1`, `diag(1,1,p)` and `diag(1,p,p)`. -/
noncomputable def stdMat : Fin 3 → Matrix.GeneralLinearGroup (Fin 3) (Localization.Away p) :=
  ![1, dgUnit ![1, 1, pUnit A p], dgUnit ![1, pUnit A p, pUnit A p]]

/-- The standard vertices `[A³]`, `[A ⊕ A ⊕ pA]` and `[A ⊕ pA ⊕ pA]`. -/
noncomputable def stdVertex (i : Fin 3) : Vertex A (Localization.Away p) p :=
  vertexOf A (Localization.Away p) p (stdMat A p i)

theorem stdVertex_zero : stdVertex A p 0 = baseVertex A (Localization.Away p) p :=
  rfl

end Standard

end BTri
end BooneHigmanLinear
end GroupApproximation
