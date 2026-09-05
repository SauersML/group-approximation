import GroupApproximation.Analysis.LIXLimitTower
import GroupApproximation.Analysis.LIXFiniteStageNullHomotopy
import GroupApproximation.Analysis.CStarCompletionCoe
import GroupApproximation.Analysis.CStarUnitaryComponent

/-!
# The inductive limit of a tower of C⋆-algebras, and persistence of a unitary

`Analysis/LIXLimitTower` builds the algebraic colimit `T.Colim` of a tower `T` of unital
C⋆-algebras as a *pre*-C⋆-algebra.  Completing it gives the C⋆-algebra of the inductive system,

    T.Limit := UniformSpace.Completion T.Colim,

which is the object STW Problem LIX needs: a unital C⋆-algebra with isometric unital
⋆-homomorphisms `T.limIota i : A i →⋆ₐ[ℂ] T.Limit` compatible with the connecting maps, whose
images `T.stage i` are closed unital ⋆-subalgebras, increasing, with dense union.

With those in hand `Analysis/LIXFiniteStageNullHomotopy` applies verbatim, and its
contrapositive is the statement the LIX argument consumes:

    T.notMem_unitaryComponentOne_limit :
      (∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j)) →
        unitaryHom (T.limIota k) u ∉ unitaryComponentOne T.Limit

— *a unitary of one stage which is null-homotopic in no later stage is not null-homotopic in the
limit*.  Without it, finite-stage nontriviality would only be evidence for, not a proof of,
nontriviality in the limit.

## How the stage is un-embedded

The one step needing care is the converse traffic.  `LIXFiniteStageNullHomotopy` produces a path
of unitaries *of the limit* which stays inside the image of `A j`; the hypothesis to contradict
lives in `A j` itself.  Moving the path back needs a continuous inverse of `T.limIota j` on its
range, and that is exactly what `Function.invFun` supplies once one knows the distance identity

    dist (T.limIotaInv j x) (T.limIotaInv j y) = dist x y   for `x, y` in the range,

which is `T.limIota j` being isometric.  No C⋆-structure on the subalgebra and no functional
calculus is involved; the map back is just an isometry of metric spaces, and `Path.map` carries
the path along it.
-/

namespace GroupApproximation

namespace LIX

universe u

noncomputable section

/-! ### Unitary groups along a ⋆-homomorphism -/

section UnitaryHom

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

/-- A ⋆-homomorphism of C⋆-algebras is contractive, hence continuous. -/
theorem continuous_of_starAlgHom (f : B →⋆ₐ[ℂ] C) : Continuous f :=
  AddMonoidHomClass.continuous_of_bound f 1 fun x => by
    simpa using NonUnitalStarAlgHom.norm_apply_le f x

/-- The homomorphism of unitary groups induced by a unital ⋆-homomorphism. -/
def unitaryHom (f : B →⋆ₐ[ℂ] C) : unitary B →* unitary C where
  toFun u := ⟨f (u : B), Unitary.map_mem f u.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' _ _ := Subtype.ext (map_mul f _ _)

@[simp] theorem coe_unitaryHom (f : B →⋆ₐ[ℂ] C) (u : unitary B) :
    ((unitaryHom f u : unitary C) : C) = f (u : B) := rfl

theorem continuous_unitaryHom (f : B →⋆ₐ[ℂ] C) : Continuous (unitaryHom f) := by
  have h : Continuous fun u : unitary B => (⟨f (u : B), Unitary.map_mem f u.2⟩ : unitary C) :=
    Continuous.subtype_mk ((continuous_of_starAlgHom f).comp continuous_subtype_val) _
  exact h

/-- A unital ⋆-homomorphism carries `U₀` into `U₀`. -/
theorem unitaryHom_mem_unitaryComponentOne (f : B →⋆ₐ[ℂ] C) {u : unitary B}
    (hu : u ∈ unitaryComponentOne B) : unitaryHom f u ∈ unitaryComponentOne C :=
  mapsTo_pathComponentOne (unitaryHom f) (continuous_unitaryHom f) hu

end UnitaryHom

namespace CStarTower

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- The inductive limit of the tower: the completion of its algebraic colimit.  This is a unital
C⋆-algebra by `CStarCompletion.completionCStarAlgebra`. -/
abbrev Limit (T : CStarTower A) : Type u := UniformSpace.Completion T.Colim

variable (T : CStarTower A)

/-! ### The canonical maps into the limit -/

/-- The canonical map of level `i` into the limit. -/
def limIota (i : ℕ) : A i →⋆ₐ[ℂ] T.Limit :=
  (CStarCompletion.coeStarAlgHom T.Colim).comp (T.iota i)

theorem limIota_apply (i : ℕ) (a : A i) :
    T.limIota i a = CStarCompletion.coeStarAlgHom T.Colim (T.iota i a) := rfl

@[simp] theorem norm_limIota (i : ℕ) (a : A i) : ‖T.limIota i a‖ = ‖a‖ := by
  rw [T.limIota_apply, CStarCompletion.norm_coeStarAlgHom, T.norm_iota]

theorem limIota_isometry (i : ℕ) : Isometry (T.limIota i) :=
  AddMonoidHomClass.isometry_of_norm _ (T.norm_limIota i)

theorem limIota_injective (i : ℕ) : Function.Injective (T.limIota i) :=
  (T.limIota_isometry i).injective

@[simp] theorem limIota_climb {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.limIota i (T.climb i k a) = T.limIota k a := by
  rw [T.limIota_apply, T.limIota_apply, T.iota_climb h]

theorem limIota_climbHom {k i : ℕ} (h : k ≤ i) (a : A k) :
    T.limIota i (T.climbHom h a) = T.limIota k a :=
  T.limIota_climb h a

instance instNontrivialLimit [Nontrivial (A 0)] : Nontrivial T.Limit :=
  (T.limIota_injective 0).nontrivial

/-! ### The stages -/

/-- The `i`-th stage of the limit: the image of `A i`, a unital ⋆-subalgebra. -/
def stage (i : ℕ) : StarSubalgebra ℂ T.Limit := (T.limIota i).range

theorem mem_stage_iff {i : ℕ} {x : T.Limit} :
    x ∈ T.stage i ↔ ∃ a : A i, T.limIota i a = x := Iff.rfl

theorem limIota_mem_stage (i : ℕ) (a : A i) : T.limIota i a ∈ T.stage i := ⟨a, rfl⟩

theorem coe_stage (i : ℕ) : (T.stage i : Set T.Limit) = Set.range (T.limIota i) := rfl

/-- Each stage is closed: it is the image of a complete space under an isometry. -/
theorem isClosed_stage (i : ℕ) : IsClosed ((T.stage i : Set T.Limit)) := by
  rw [T.coe_stage]
  exact (T.limIota_isometry i).isClosedEmbedding.isClosed_range

theorem stage_mono : Monotone T.stage := by
  intro k i h x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨T.climb i k a, T.limIota_climb h a⟩

/-- The stages exhaust the limit. -/
theorem dense_iUnion_stage : Dense (⋃ i, (T.stage i : Set T.Limit)) := by
  intro x
  refine closure_mono ?_ (CStarCompletion.denseRange_coeStarAlgHom T.Colim x)
  rintro y ⟨z, rfl⟩
  obtain ⟨i, a, rfl⟩ := T.exists_iota z
  exact Set.mem_iUnion.mpr ⟨i, T.limIota_mem_stage i a⟩

/-! ### The inverse of a stage embedding -/

/-- The inverse of `T.limIota i` on its range (junk elsewhere). -/
def limIotaInv (i : ℕ) (x : T.Limit) : A i := Function.invFun (T.limIota i) x

theorem limIota_limIotaInv {i : ℕ} {x : T.Limit} (hx : x ∈ T.stage i) :
    T.limIota i (T.limIotaInv i x) = x :=
  Function.invFun_eq (T.mem_stage_iff.mp hx)

@[simp] theorem limIotaInv_limIota (i : ℕ) (a : A i) : T.limIotaInv i (T.limIota i a) = a :=
  Function.leftInverse_invFun (T.limIota_injective i) a

theorem dist_limIotaInv {i : ℕ} {x y : T.Limit} (hx : x ∈ T.stage i) (hy : y ∈ T.stage i) :
    dist (T.limIotaInv i x) (T.limIotaInv i y) = dist x y := by
  conv_rhs => rw [← T.limIota_limIotaInv hx, ← T.limIota_limIotaInv hy]
  exact ((T.limIota_isometry i).dist_eq _ _).symm

theorem isometry_limIotaInv (i : ℕ) :
    Isometry fun x : {x : T.Limit // x ∈ Set.range (T.limIota i)} =>
      T.limIotaInv i (x : T.Limit) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [Subtype.dist_eq]
  exact T.dist_limIotaInv x.2 y.2

/-- A unitary of the limit lying in the `i`-th stage comes from a unitary of `A i`. -/
theorem limIotaInv_mem_unitary {i : ℕ} {x : T.Limit} (hx : x ∈ T.stage i)
    (hxu : x ∈ unitary T.Limit) : T.limIotaInv i x ∈ unitary (A i) := by
  rw [Unitary.mem_iff] at hxu ⊢
  constructor
  · refine T.limIota_injective i ?_
    rw [map_mul, map_star, T.limIota_limIotaInv hx, map_one]
    exact hxu.1
  · refine T.limIota_injective i ?_
    rw [map_mul, map_star, T.limIota_limIotaInv hx, map_one]
    exact hxu.2

/-- The inverse of `T.limIota i`, read on the unitaries lying in the `i`-th stage. -/
def stageUnitaryInv (i : ℕ) (w : unitaryIn (T.stage i)) : unitary (A i) :=
  ⟨T.limIotaInv i ((w : unitary T.Limit) : T.Limit),
    T.limIotaInv_mem_unitary w.2 (w : unitary T.Limit).2⟩

theorem coe_stageUnitaryInv (i : ℕ) (w : unitaryIn (T.stage i)) :
    ((T.stageUnitaryInv i w : unitary (A i)) : A i)
      = T.limIotaInv i ((w : unitary T.Limit) : T.Limit) := rfl

theorem continuous_stageUnitaryInv (i : ℕ) : Continuous (T.stageUnitaryInv i) := by
  have h₁ : Continuous fun w : unitaryIn (T.stage i) =>
      (⟨((w : unitary T.Limit) : T.Limit), T.mem_stage_iff.mp w.2⟩ :
        {x : T.Limit // x ∈ Set.range (T.limIota i)}) :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have h₂ : Continuous fun w : unitaryIn (T.stage i) =>
      (⟨T.limIotaInv i ((w : unitary T.Limit) : T.Limit),
        T.limIotaInv_mem_unitary w.2 (w : unitary T.Limit).2⟩ : unitary (A i)) :=
    Continuous.subtype_mk ((T.isometry_limIotaInv i).continuous.comp h₁) _
  exact h₂

/-! ### Persistence -/

/-- A null-homotopy of `T.limIota i u` that stays inside the `i`-th stage is a null-homotopy of
`u` in `A i`: push the path back through the isometric inverse of the stage embedding. -/
theorem joined_of_joinedIn_stage {i : ℕ} {u : unitary (A i)}
    (h : JoinedIn (unitaryIn (T.stage i)) 1 (unitaryHom (T.limIota i) u)) :
    Joined (1 : unitary (A i)) u := by
  obtain ⟨γ⟩ := h.joined_subtype
  refine ⟨(γ.map (T.continuous_stageUnitaryInv i)).cast ?_ ?_⟩
  · refine Subtype.ext ?_
    show ((1 : unitary (A i)) : A i) = T.limIotaInv i ((1 : unitary T.Limit) : T.Limit)
    simp only [OneMemClass.coe_one]
    rw [← map_one (T.limIota i), T.limIotaInv_limIota]
  · refine Subtype.ext ?_
    show (u : A i) = T.limIotaInv i ((unitaryHom (T.limIota i) u : unitary T.Limit) : T.Limit)
    rw [coe_unitaryHom, T.limIotaInv_limIota]

/-- **Persistence of a nontrivial unitary in the inductive limit.**  A unitary of the stage `A k`
whose image in *every* later stage fails to be null-homotopic there has a non-null-homotopic
image in the limit.

This is `LIXFiniteStageNullHomotopy.exists_ge_joinedIn_one_of_joined` — a null-homotopy in the
limit may be replaced by one inside a single later stage — combined with the transport of that
stage-wise homotopy back into `A j`. -/
theorem notMem_unitaryComponentOne_limit {k : ℕ} {u : unitary (A k)}
    (h : ∀ (j : ℕ) (hj : k ≤ j),
      unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j)) :
    unitaryHom (T.limIota k) u ∉ unitaryComponentOne T.Limit := by
  intro hmem
  have hak : ((unitaryHom (T.limIota k) u : unitary T.Limit) : T.Limit) ∈ T.stage k :=
    ⟨(u : A k), rfl⟩
  obtain ⟨j, hkj, hj⟩ :=
    exists_ge_joinedIn_one_of_joined (S := T.stage) (fun i => T.isClosed_stage i)
      T.stage_mono T.dense_iUnion_stage hak hmem
  have hval : unitaryHom (T.limIota k) u
      = unitaryHom (T.limIota j) (unitaryHom (T.climbHom hkj) u) := by
    refine Subtype.ext ?_
    show T.limIota k (u : A k) = T.limIota j (T.climb j k (u : A k))
    rw [T.limIota_climb hkj]
  rw [hval] at hj
  exact h j hkj (T.joined_of_joinedIn_stage hj)

end CStarTower

end

end LIX

end GroupApproximation
