import GroupApproximation.KTheory.K0Basic

/-!
# `K₀` of a direct sum

For `*`-rings `A` and `B`, `K₀(A × B) ≃+ K₀(A) × K₀(B)`. The forward map is induced by the two
coordinate projections, the inverse by the two corner inclusions `a ↦ (a, 0)`, `b ↦ (0, b)`.

* `KZero.map_eq_zero`: a `*`-homomorphism that kills everything induces the zero map.
* `KZero.prodEquiv`: `K₀(A × B) ≃+ K₀(A) × K₀(B)`; for unital `A`, `B` it sends `[1]` to
  `([1], [1])` (`KZero.prodEquiv_unitClass`).

The inverse law on classes of projections is orthogonal additivity: a projection `p` over `A × B`
is the orthogonal sum of its two corners `(p.1, 0)` and `(0, p.2)`.
-/

namespace GroupApproximation
namespace KTheory

open scoped Matrix

section StarProd

variable (A B : Type*) [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]

/-- The first coordinate projection `A × B → A` as a `*`-homomorphism. -/
def starFst : A × B →⋆ₙ+* A :=
  { NonUnitalRingHom.fst A B with map_star' := fun _ => rfl }

/-- The second coordinate projection `A × B → B` as a `*`-homomorphism. -/
def starSnd : A × B →⋆ₙ+* B :=
  { NonUnitalRingHom.snd A B with map_star' := fun _ => rfl }

/-- The corner inclusion `a ↦ (a, 0)` as a `*`-homomorphism. -/
def starInl : A →⋆ₙ+* A × B where
  toFun a := (a, 0)
  map_mul' a b := by simp
  map_zero' := rfl
  map_add' a b := by simp
  map_star' a := by simp [Prod.ext_iff]

/-- The corner inclusion `b ↦ (0, b)` as a `*`-homomorphism. -/
def starInr : B →⋆ₙ+* A × B where
  toFun b := (0, b)
  map_mul' a b := by simp
  map_zero' := rfl
  map_add' a b := by simp
  map_star' b := by simp [Prod.ext_iff]

variable {A B}

@[simp] theorem starFst_apply (x : A × B) : starFst A B x = x.1 := rfl

@[simp] theorem starSnd_apply (x : A × B) : starSnd A B x = x.2 := rfl

@[simp] theorem starInl_apply (a : A) : starInl A B a = (a, 0) := rfl

@[simp] theorem starInr_apply (b : B) : starInr A B b = (0, b) := rfl

theorem starFst_comp_starInl : (starFst A B).comp (starInl A B) = NonUnitalStarRingHom.id A :=
  NonUnitalStarRingHom.ext fun _ => rfl

theorem starSnd_comp_starInr : (starSnd A B).comp (starInr A B) = NonUnitalStarRingHom.id B :=
  NonUnitalStarRingHom.ext fun _ => rfl

end StarProd

namespace KZero

variable {A B : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]

/-- A `*`-homomorphism with zero values induces the zero map on `K₀`. -/
theorem map_eq_zero {f : A →⋆ₙ+* B} (hf : ∀ a, f a = 0) : map f = 0 := by
  refine hom_ext fun x => ?_
  obtain ⟨n, p, hp⟩ := x
  have h : Cycle.map f ⟨n, p, hp⟩ = ⟨n, 0, IsStarProjection.zero _⟩ :=
    Cycle.eq_of_proj_eq (Matrix.ext fun i j => hf (p i j))
  rw [map_mk, h, mk_zero_proj, AddMonoidHom.zero_apply]

theorem map_starFst_map_starInl (a : KZero A) :
    map (starFst A B) (map (starInl A B) a) = a := by
  have h : (map (starFst A B)).comp (map (starInl A B)) = AddMonoidHom.id _ := by
    rw [← map_comp, starFst_comp_starInl, map_id]
  exact DFunLike.congr_fun h a

theorem map_starSnd_map_starInr (b : KZero B) :
    map (starSnd A B) (map (starInr A B) b) = b := by
  have h : (map (starSnd A B)).comp (map (starInr A B)) = AddMonoidHom.id _ := by
    rw [← map_comp, starSnd_comp_starInr, map_id]
  exact DFunLike.congr_fun h b

theorem map_starSnd_map_starInl (a : KZero A) :
    map (starSnd A B) (map (starInl A B) a) = 0 := by
  have h : (map (starSnd A B)).comp (map (starInl A B)) = 0 := by
    rw [← map_comp]
    exact map_eq_zero fun _ => rfl
  exact DFunLike.congr_fun h a

theorem map_starFst_map_starInr (b : KZero B) :
    map (starFst A B) (map (starInr A B) b) = 0 := by
  have h : (map (starFst A B)).comp (map (starInr A B)) = 0 := by
    rw [← map_comp]
    exact map_eq_zero fun _ => rfl
  exact DFunLike.congr_fun h b

variable (A B) in
/-- The coordinate map `K₀(A × B) → K₀(A) × K₀(B)`. -/
noncomputable def prodHom : KZero (A × B) →+ KZero A × KZero B :=
  (map (starFst A B)).prod (map (starSnd A B))

variable (A B) in
/-- The corner map `K₀(A) × K₀(B) → K₀(A × B)`. -/
noncomputable def coprodHom : KZero A × KZero B →+ KZero (A × B) :=
  (map (starInl A B)).coprod (map (starInr A B))

theorem coprodHom_comp_prodHom : (coprodHom A B).comp (prodHom A B) = AddMonoidHom.id _ := by
  refine hom_ext fun x => ?_
  obtain ⟨n, p, hp⟩ := x
  have hmul : (p.map (starFst A B)).map (starInl A B) *
      (p.map (starSnd A B)).map (starInr A B) = 0 := by
    ext i j <;> simp [Matrix.mul_apply]
  have hsum : (p.map (starFst A B)).map (starInl A B) +
      (p.map (starSnd A B)).map (starInr A B) = p := by
    ext i j <;> simp
  have h := mk_add_of_mul_eq_zero
    (isStarProjection_map (starInl A B) (isStarProjection_map (starFst A B) hp))
    (isStarProjection_map (starInr A B) (isStarProjection_map (starSnd A B) hp)) hmul
  show map (starInl A B) (map (starFst A B) (mk ⟨n, p, hp⟩)) +
      map (starInr A B) (map (starSnd A B) (mk ⟨n, p, hp⟩)) = mk ⟨n, p, hp⟩
  rw [map_mk, map_mk, map_mk, map_mk]
  exact h.symm.trans (congrArg mk (Cycle.eq_of_proj_eq hsum))

theorem prodHom_comp_coprodHom : (prodHom A B).comp (coprodHom A B) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  show (map (starFst A B) (map (starInl A B) a + map (starInr A B) b),
      map (starSnd A B) (map (starInl A B) a + map (starInr A B) b)) = (a, b)
  rw [_root_.map_add, _root_.map_add, map_starFst_map_starInl, map_starSnd_map_starInl,
    map_starFst_map_starInr, map_starSnd_map_starInr, add_zero, zero_add]

variable (A B) in
/-- **`K₀` of a direct sum**: `K₀(A × B) ≃+ K₀(A) × K₀(B)`. -/
noncomputable def prodEquiv : KZero (A × B) ≃+ KZero A × KZero B :=
  AddMonoidHom.toAddEquiv (prodHom A B) (coprodHom A B) coprodHom_comp_prodHom
    prodHom_comp_coprodHom

@[simp] theorem prodEquiv_apply (y : KZero (A × B)) :
    prodEquiv A B y = (map (starFst A B) y, map (starSnd A B) y) := rfl

@[simp] theorem prodEquiv_symm_apply (ab : KZero A × KZero B) :
    (prodEquiv A B).symm ab = map (starInl A B) ab.1 + map (starInr A B) ab.2 := rfl

end KZero

/-- For unital `A` and `B`, the direct sum isomorphism sends `[1]` to `([1], [1])`. -/
theorem KZero.prodEquiv_unitClass {A B : Type*} [Semiring A] [StarRing A] [Semiring B]
    [StarRing B] :
    KZero.prodEquiv A B (KZero.unitClass (A × B)) = (KZero.unitClass A, KZero.unitClass B) := by
  rw [KZero.prodEquiv_apply, KZero.map_unitClass (starFst A B) rfl,
    KZero.map_unitClass (starSnd A B) rfl]

end KTheory
end GroupApproximation
