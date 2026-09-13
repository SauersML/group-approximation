import GroupApproximation.Analysis.LIXLimitCompletion
import GroupApproximation.Analysis.CStarCompletionHom
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The universal property of a sequential C⋆-inductive limit

`Analysis/LIXLimitTower` and `Analysis/LIXLimitCompletion` build, for a tower
`A 0 → A 1 → A 2 → ⋯` of unital C⋆-algebras whose connecting maps are isometric unital
⋆-homomorphisms, the algebraic colimit `T.Colim`, its completion `T.Limit`, and the canonical
maps `T.limIota i : A i →⋆ₐ[ℂ] T.Limit`.  What makes `T.Limit` *the* inductive limit is its
universal property, and this file proves it.

## Main declarations

* `CStarTower.Compatible T φ`: a family `φ i : A i →⋆ₐ[ℂ] B` with `φ (i + 1) ∘ succHom i = φ i`.
* `CStarTower.limLift T φ hφ : T.Limit →⋆ₐ[ℂ] B`, with `limLift_limIota`, `limLift_unique` and
  `existsUnique_limLift`.  The target `B` lives in an arbitrary universe.
* `CStarTower.limit_hom_ext`: ⋆-homomorphisms out of the limit that agree on every stage agree.
* `CStarTower.norm_limLift`: a compatible family of injective ⋆-homomorphisms lifts to an
  isometry.  `CStarTower.limLiftEquiv`: if moreover `⋃ i, range (φ i)` is dense in `B`, then `B`
  is the limit.  This recognition criterion identifies a concrete algebra as an inductive limit.
* `CStarTower.Intertwines`, `CStarTower.limMap`, `limMap_id`, `limMap_comp`: functoriality in
  morphisms of towers, and `CStarTower.limEquiv` for levelwise ⋆-isomorphisms.
* `CStarTower.shift` and `CStarTower.shiftEquiv`: removing the first level does not change the
  limit.

## How the lift is built

On the algebraic colimit the value at a point is `φ i a` for any representative `(i, a)`.  Two
representatives climb to a common level, where they agree because `T.iota` is injective, and a
compatible family commutes with climbing.  The lift is contractive because a ⋆-homomorphism of
C⋆-algebras is, so it extends across the completion by `CStarCompletion.extendStarAlgHom`.
Uniqueness is density of the union of the stages.

## References

* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 6
  (inductive limits of C⋆-algebras).
* B. Blackadar, *Operator Algebras*, Section II.8 (inductive limits).
-/

namespace GroupApproximation

namespace LIX

universe u u' u'' v w

noncomputable section

namespace CStarTower

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
variable {B : Type v} [CStarAlgebra B]

/-! ### Compatible families -/

section Compatible

variable (T : CStarTower A)

/-- A family of unital ⋆-homomorphisms out of the levels of a tower is **compatible** when it
commutes with the connecting maps: `φ (i + 1) ∘ succHom i = φ i`. -/
def Compatible (φ : ∀ i, A i →⋆ₐ[ℂ] B) : Prop :=
  ∀ (i : ℕ) (a : A i), φ (i + 1) (T.succHom i a) = φ i a

/-- The canonical maps into the limit form a compatible family. -/
theorem compatible_limIota : T.Compatible T.limIota := T.limIota_succHom

variable {T}

/-- A compatible family commutes with every iterated connecting map. -/
theorem Compatible.climb {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ) {k i : ℕ} (h : k ≤ i)
    (a : A k) : φ i (T.climb i k a) = φ k a := by
  induction i, h using Nat.le_induction with
  | base => rw [T.climb_self]
  | succ n hkn ih => rw [T.climb_succ hkn, hφ n, ih]

/-- A compatible family takes one value on all representatives of a point of the colimit. -/
theorem Compatible.eq_of_iota_eq {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ) {i j : ℕ}
    {a : A i} {b : A j} (h : T.iota i a = T.iota j b) : φ i a = φ j b := by
  have hc : T.climb (max i j) i a = T.climb (max i j) j b := by
    apply T.iota_injective (max i j)
    rw [T.iota_climb (le_max_left i j), T.iota_climb (le_max_right i j), h]
  rw [← hφ.climb (le_max_left i j) a, ← hφ.climb (le_max_right i j) b, hc]

/-- Composing a compatible family with a ⋆-homomorphism keeps it compatible. -/
theorem Compatible.comp {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ) {C : Type w}
    [CStarAlgebra C] (g : B →⋆ₐ[ℂ] C) : T.Compatible fun i ↦ g.comp (φ i) :=
  fun i a ↦ congrArg g (hφ i a)

end Compatible

/-! ### The lift on the algebraic colimit -/

section ColimLift

variable (T : CStarTower A)

/-- Any two points of the colimit are represented at a common level. -/
theorem exists_iota_pair (z w : T.Colim) :
    ∃ (i : ℕ) (a b : A i), z = T.iota i a ∧ w = T.iota i b := by
  obtain ⟨i, a, rfl⟩ := T.exists_iota z
  obtain ⟨j, b, rfl⟩ := T.exists_iota w
  exact ⟨max i j, T.climb (max i j) i a, T.climb (max i j) j b,
    (T.iota_climb (le_max_left i j) a).symm, (T.iota_climb (le_max_right i j) b).symm⟩

/-- The function underlying `colimLift`: the value of `φ` at a chosen representative. -/
def colimLiftFun (φ : ∀ i, A i →⋆ₐ[ℂ] B) (z : T.Colim) : B :=
  φ (T.exists_iota z).choose (T.exists_iota z).choose_spec.choose

theorem colimLiftFun_iota {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ) (i : ℕ) (a : A i) :
    T.colimLiftFun φ (T.iota i a) = φ i a :=
  hφ.eq_of_iota_eq (T.exists_iota (T.iota i a)).choose_spec.choose_spec.symm

/-- **The lift of a compatible family to the algebraic colimit.** -/
def colimLift (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) : T.Colim →⋆ₐ[ℂ] B where
  toFun := T.colimLiftFun φ
  map_one' := by
    have h := T.colimLiftFun_iota hφ 0 1
    rw [map_one (T.iota 0), map_one (φ 0)] at h
    exact h
  map_mul' z w := by
    obtain ⟨i, a, b, rfl, rfl⟩ := T.exists_iota_pair z w
    have h := T.colimLiftFun_iota hφ i (a * b)
    rw [map_mul (T.iota i) a b, map_mul (φ i) a b, ← T.colimLiftFun_iota hφ i a,
      ← T.colimLiftFun_iota hφ i b] at h
    exact h
  map_zero' := by
    have h := T.colimLiftFun_iota hφ 0 0
    rw [map_zero (T.iota 0), map_zero (φ 0)] at h
    exact h
  map_add' z w := by
    obtain ⟨i, a, b, rfl, rfl⟩ := T.exists_iota_pair z w
    have h := T.colimLiftFun_iota hφ i (a + b)
    rw [map_add (T.iota i) a b, map_add (φ i) a b, ← T.colimLiftFun_iota hφ i a,
      ← T.colimLiftFun_iota hφ i b] at h
    exact h
  commutes' r := by
    have h := T.colimLiftFun_iota hφ 0 (algebraMap ℂ (A 0) r)
    rw [AlgHomClass.commutes (T.iota 0) r, AlgHomClass.commutes (φ 0) r] at h
    exact h
  map_star' z := by
    obtain ⟨i, a, rfl⟩ := T.exists_iota z
    have h := T.colimLiftFun_iota hφ i (star a)
    rw [StarHomClass.map_star (T.iota i) a, StarHomClass.map_star (φ i) a,
      ← T.colimLiftFun_iota hφ i a] at h
    exact h

@[simp] theorem colimLift_iota (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) (i : ℕ)
    (a : A i) : T.colimLift φ hφ (T.iota i a) = φ i a :=
  T.colimLiftFun_iota hφ i a

/-- The lift on the colimit is contractive for the colimit norm. -/
theorem norm_colimLift_le (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) (z : T.Colim) :
    ‖T.colimLift φ hφ z‖ ≤ ‖z‖ := by
  obtain ⟨i, a, rfl⟩ := T.exists_iota z
  rw [T.colimLift_iota φ hφ i a, T.norm_iota i a]
  exact NonUnitalStarAlgHom.norm_apply_le (φ i) a

theorem uniformContinuous_colimLift (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) :
    UniformContinuous (T.colimLift φ hφ : T.Colim → B) :=
  CStarCompletion.uniformContinuous_of_norm_le _ (T.norm_colimLift_le φ hφ)

end ColimLift

/-! ### The universal property of the limit -/

section LimLift

variable (T : CStarTower A)

/-- **The universal map out of the inductive limit.**  A compatible family of unital
⋆-homomorphisms `φ i : A i →⋆ₐ[ℂ] B` induces a unital ⋆-homomorphism `T.Limit →⋆ₐ[ℂ] B`. -/
def limLift (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) : T.Limit →⋆ₐ[ℂ] B :=
  CStarCompletion.extendStarAlgHom (T.colimLift φ hφ) (T.uniformContinuous_colimLift φ hφ)

@[simp] theorem limLift_limIota (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) (i : ℕ)
    (a : A i) : T.limLift φ hφ (T.limIota i a) = φ i a := by
  rw [T.limIota_apply, CStarCompletion.coeStarAlgHom_apply]
  exact (CStarCompletion.extendStarAlgHom_coe (T.colimLift φ hφ)
    (T.uniformContinuous_colimLift φ hφ) (T.iota i a)).trans (T.colimLift_iota φ hφ i a)

/-- **⋆-homomorphisms out of the limit are determined on the stages.** -/
theorem limit_hom_ext {f g : T.Limit →⋆ₐ[ℂ] B}
    (h : ∀ (i : ℕ) (a : A i), f (T.limIota i a) = g (T.limIota i a)) : f = g := by
  have hfg : (f : T.Limit → B) = g := by
    refine Continuous.ext_on T.dense_iUnion_stage (continuous_of_starAlgHom f)
      (continuous_of_starAlgHom g) ?_
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, rfl⟩ := T.mem_stage_iff.mp hi
    exact h i a
  exact StarAlgHom.ext (congrFun hfg)

theorem limLift_unique (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) (g : T.Limit →⋆ₐ[ℂ] B)
    (hg : ∀ (i : ℕ) (a : A i), g (T.limIota i a) = φ i a) : g = T.limLift φ hφ :=
  T.limit_hom_ext fun i a ↦ (hg i a).trans (T.limLift_limIota φ hφ i a).symm

/-- **The universal property of the inductive limit**, for a target in any universe. -/
theorem existsUnique_limLift (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) :
    ∃! f : T.Limit →⋆ₐ[ℂ] B, ∀ (i : ℕ) (a : A i), f (T.limIota i a) = φ i a :=
  ⟨T.limLift φ hφ, T.limLift_limIota φ hφ, fun g hg ↦ T.limLift_unique φ hφ g hg⟩

@[simp] theorem limLift_limIota_eq_id :
    T.limLift T.limIota T.compatible_limIota = StarAlgHom.id ℂ T.Limit :=
  (T.limLift_unique T.limIota T.compatible_limIota (StarAlgHom.id ℂ T.Limit)
    fun _ _ ↦ rfl).symm

theorem comp_limLift (φ : ∀ i, A i →⋆ₐ[ℂ] B) (hφ : T.Compatible φ) {C : Type w}
    [CStarAlgebra C] (g : B →⋆ₐ[ℂ] C) :
    g.comp (T.limLift φ hφ) = T.limLift (fun i ↦ g.comp (φ i)) (hφ.comp g) :=
  T.limLift_unique _ _ _ fun i a ↦ congrArg g (T.limLift_limIota φ hφ i a)

/-- A compatible family of injective ⋆-homomorphisms lifts to an isometry: the two norms are
continuous on the limit and agree on the dense union of the stages. -/
theorem norm_limLift {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) (x : T.Limit) : ‖T.limLift φ hφ x‖ = ‖x‖ := by
  have h : (fun x : T.Limit ↦ ‖T.limLift φ hφ x‖) = fun x ↦ ‖x‖ := by
    refine Continuous.ext_on T.dense_iUnion_stage
      (continuous_of_starAlgHom (T.limLift φ hφ)).norm continuous_norm ?_
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, rfl⟩ := T.mem_stage_iff.mp hi
    show ‖T.limLift φ hφ (T.limIota i a)‖ = ‖T.limIota i a‖
    rw [T.limLift_limIota, T.norm_limIota]
    exact NonUnitalStarAlgHom.norm_map (φ i) (hinj i) a
  exact congrFun h x

theorem isometry_limLift {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) : Isometry (T.limLift φ hφ) :=
  AddMonoidHomClass.isometry_of_norm _ (T.norm_limLift hφ hinj)

theorem injective_limLift {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) : Function.Injective (T.limLift φ hφ) :=
  (T.isometry_limLift hφ hinj).injective

/-- The lift of an injective compatible family is onto once the union of the images is dense:
its range is closed, being isometric from a complete space, and contains that union. -/
theorem surjective_limLift {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) (hdense : Dense (⋃ i, Set.range (φ i))) :
    Function.Surjective (T.limLift φ hφ) := by
  have hclosed : IsClosed (Set.range (T.limLift φ hφ)) :=
    (T.isometry_limLift hφ hinj).isClosedEmbedding.isClosed_range
  have hsub : (⋃ i, Set.range (φ i)) ⊆ Set.range (T.limLift φ hφ) := by
    intro y hy
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨T.limIota i a, T.limLift_limIota φ hφ i a⟩
  exact Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans (hdense.mono hsub).closure_eq)

/-- **Recognition of an inductive limit.**  A C⋆-algebra `B` with a compatible family of
injective unital ⋆-homomorphisms `φ i : A i → B` whose images have dense union is ⋆-isomorphic
to the limit, by the map carrying `T.limIota i a` to `φ i a`. -/
def limLiftEquiv {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) (hdense : Dense (⋃ i, Set.range (φ i))) :
    T.Limit ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective (T.limLift φ hφ)
    ⟨T.injective_limLift hφ hinj, T.surjective_limLift hφ hinj hdense⟩

@[simp] theorem limLiftEquiv_limIota {φ : ∀ i, A i →⋆ₐ[ℂ] B} (hφ : T.Compatible φ)
    (hinj : ∀ i, Function.Injective (φ i)) (hdense : Dense (⋃ i, Set.range (φ i))) (i : ℕ)
    (a : A i) : T.limLiftEquiv hφ hinj hdense (T.limIota i a) = φ i a :=
  T.limLift_limIota φ hφ i a

end LimLift

/-! ### Morphisms of towers -/

section Morphism

variable {A' : ℕ → Type u'} [∀ n, CStarAlgebra (A' n)]
variable {A'' : ℕ → Type u''} [∀ n, CStarAlgebra (A'' n)]
variable (T : CStarTower A)

/-- A **morphism of towers** `T → S`: levelwise unital ⋆-homomorphisms intertwining the
connecting maps. -/
def Intertwines (S : CStarTower A') (ψ : ∀ i, A i →⋆ₐ[ℂ] A' i) : Prop :=
  ∀ (i : ℕ) (a : A i), ψ (i + 1) (T.succHom i a) = S.succHom i (ψ i a)

variable {T} in
theorem Intertwines.compatible {S : CStarTower A'} {ψ : ∀ i, A i →⋆ₐ[ℂ] A' i}
    (hψ : T.Intertwines S ψ) : T.Compatible fun i ↦ (S.limIota i).comp (ψ i) := fun i a ↦ by
  show S.limIota (i + 1) (ψ (i + 1) (T.succHom i a)) = S.limIota i (ψ i a)
  rw [hψ i a, S.limIota_succHom]

/-- **The map of limits induced by a morphism of towers.** -/
def limMap (S : CStarTower A') (ψ : ∀ i, A i →⋆ₐ[ℂ] A' i) (hψ : T.Intertwines S ψ) :
    T.Limit →⋆ₐ[ℂ] S.Limit :=
  T.limLift (fun i ↦ (S.limIota i).comp (ψ i)) hψ.compatible

@[simp] theorem limMap_limIota (S : CStarTower A') (ψ : ∀ i, A i →⋆ₐ[ℂ] A' i)
    (hψ : T.Intertwines S ψ) (i : ℕ) (a : A i) :
    T.limMap S ψ hψ (T.limIota i a) = S.limIota i (ψ i a) :=
  T.limLift_limIota _ hψ.compatible i a

theorem intertwines_id : T.Intertwines T fun i ↦ StarAlgHom.id ℂ (A i) := fun _ _ ↦ rfl

@[simp] theorem limMap_id :
    T.limMap T (fun i ↦ StarAlgHom.id ℂ (A i)) T.intertwines_id = StarAlgHom.id ℂ T.Limit :=
  T.limit_hom_ext fun i a ↦ T.limMap_limIota T _ T.intertwines_id i a

variable {T} in
theorem Intertwines.comp {S : CStarTower A'} {R : CStarTower A''}
    {ψ : ∀ i, A i →⋆ₐ[ℂ] A' i} {χ : ∀ i, A' i →⋆ₐ[ℂ] A'' i} (hψ : T.Intertwines S ψ)
    (hχ : S.Intertwines R χ) : T.Intertwines R fun i ↦ (χ i).comp (ψ i) := fun i a ↦ by
  show χ (i + 1) (ψ (i + 1) (T.succHom i a)) = R.succHom i (χ i (ψ i a))
  rw [hψ i a, hχ i (ψ i a)]

theorem limMap_comp (S : CStarTower A') (R : CStarTower A'') (ψ : ∀ i, A i →⋆ₐ[ℂ] A' i)
    (χ : ∀ i, A' i →⋆ₐ[ℂ] A'' i) (hψ : T.Intertwines S ψ) (hχ : S.Intertwines R χ) :
    (S.limMap R χ hχ).comp (T.limMap S ψ hψ) =
      T.limMap R (fun i ↦ (χ i).comp (ψ i)) (hψ.comp hχ) :=
  T.limit_hom_ext fun i a ↦
    (congrArg (S.limMap R χ hχ) (T.limMap_limIota S ψ hψ i a)).trans
      ((S.limMap_limIota R χ hχ i (ψ i a)).trans
        (T.limMap_limIota R _ (hψ.comp hχ) i a).symm)

variable {T} in
theorem Intertwines.symm {S : CStarTower A'} {e : ∀ i, A i ≃⋆ₐ[ℂ] A' i}
    (he : T.Intertwines S fun i ↦ (e i).toStarAlgHom) :
    S.Intertwines T fun i ↦ (e i).symm.toStarAlgHom := fun i b ↦ by
  show (e (i + 1)).symm (S.succHom i b) = T.succHom i ((e i).symm b)
  apply EquivLike.injective (e (i + 1))
  rw [StarAlgEquiv.apply_symm_apply]
  exact ((he i ((e i).symm b)).trans
    (congrArg (S.succHom i) ((e i).apply_symm_apply b))).symm

/-- **Levelwise ⋆-isomorphisms of towers induce a ⋆-isomorphism of the limits.** -/
def limEquiv (S : CStarTower A') (e : ∀ i, A i ≃⋆ₐ[ℂ] A' i)
    (he : T.Intertwines S fun i ↦ (e i).toStarAlgHom) : T.Limit ≃⋆ₐ[ℂ] S.Limit :=
  StarAlgEquiv.ofStarAlgHom (T.limMap S _ he) (S.limMap T _ he.symm)
    (T.limit_hom_ext fun i a ↦
      (congrArg (S.limMap T _ he.symm) (T.limMap_limIota S _ he i a)).trans
        ((S.limMap_limIota T _ he.symm i _).trans
          (congrArg (T.limIota i) ((e i).symm_apply_apply a))))
    (S.limit_hom_ext fun i b ↦
      (congrArg (T.limMap S _ he) (S.limMap_limIota T _ he.symm i b)).trans
        ((T.limMap_limIota S _ he i _).trans
          (congrArg (S.limIota i) ((e i).apply_symm_apply b))))

@[simp] theorem limEquiv_limIota (S : CStarTower A') (e : ∀ i, A i ≃⋆ₐ[ℂ] A' i)
    (he : T.Intertwines S fun i ↦ (e i).toStarAlgHom) (i : ℕ) (a : A i) :
    T.limEquiv S e he (T.limIota i a) = S.limIota i (e i a) :=
  T.limMap_limIota S _ he i a

end Morphism

/-! ### Shifting the index -/

section Shift

variable (T : CStarTower A)

/-- The tower with its first level removed. -/
def shift : CStarTower fun n ↦ A (n + 1) where
  succHom n := T.succHom (n + 1)
  norm_succHom n := T.norm_succHom (n + 1)

@[simp] theorem shift_succHom (n : ℕ) (a : A (n + 1)) :
    T.shift.succHom n a = T.succHom (n + 1) a := rfl

/-- The limit of the shifted tower maps into the limit of the tower. -/
def shiftToLimit : T.shift.Limit →⋆ₐ[ℂ] T.Limit :=
  T.shift.limLift (fun n ↦ T.limIota (n + 1)) fun n a ↦ T.limIota_succHom (n + 1) a

/-- The limit of the tower maps into the limit of the shifted tower: level `n` enters through
the connecting map into level `n + 1`. -/
def limitToShift : T.Limit →⋆ₐ[ℂ] T.shift.Limit :=
  T.limLift (fun n ↦ (T.shift.limIota n).comp (T.succHom n))
    fun n a ↦ T.shift.limIota_succHom n (T.succHom n a)

@[simp] theorem shiftToLimit_limIota (n : ℕ) (a : A (n + 1)) :
    T.shiftToLimit (T.shift.limIota n a) = T.limIota (n + 1) a :=
  T.shift.limLift_limIota (fun n ↦ T.limIota (n + 1)) (fun n a ↦ T.limIota_succHom (n + 1) a) n a

@[simp] theorem limitToShift_limIota (n : ℕ) (a : A n) :
    T.limitToShift (T.limIota n a) = T.shift.limIota n (T.succHom n a) :=
  T.limLift_limIota (fun n ↦ (T.shift.limIota n).comp (T.succHom n))
    (fun n a ↦ T.shift.limIota_succHom n (T.succHom n a)) n a

/-- **Removing the first level of a tower does not change its limit.** -/
def shiftEquiv : T.shift.Limit ≃⋆ₐ[ℂ] T.Limit :=
  StarAlgEquiv.ofStarAlgHom T.shiftToLimit T.limitToShift
    (T.shift.limit_hom_ext fun n a ↦
      (congrArg T.limitToShift (T.shiftToLimit_limIota n a)).trans
        ((T.limitToShift_limIota (n + 1) a).trans (T.shift.limIota_succHom n a)))
    (T.limit_hom_ext fun n a ↦
      (congrArg T.shiftToLimit (T.limitToShift_limIota n a)).trans
        ((T.shiftToLimit_limIota n (T.succHom n a)).trans (T.limIota_succHom n a)))

@[simp] theorem shiftEquiv_limIota (n : ℕ) (a : A (n + 1)) :
    T.shiftEquiv (T.shift.limIota n a) = T.limIota (n + 1) a :=
  T.shiftToLimit_limIota n a

end Shift

end CStarTower

end

end LIX

end GroupApproximation
