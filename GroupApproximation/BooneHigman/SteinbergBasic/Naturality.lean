import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Steinberg.ElementaryIndexPadding

/-!
# Naturality of the Steinberg projection and of `K₂`

A unital ring homomorphism `f : R →+* S` acts coefficientwise on Steinberg groups (`SteinbergGroup.ringMap`)
and on elementary groups (`elementaryGroupMap`).  An index embedding `e : I ↪ J` acts on Steinberg groups by
relabelling (`SteinbergGroup.indexMap`) and on elementary groups by identity padding
(`ElementaryPadding.elementaryPad`).  This file proves that the canonical projection `St → E` commutes with
both actions.  So both actions carry `K₂` into `K₂`, which gives the induced maps

* `K2Map f : K₂(I,R) →* K₂(I,S)`;
* `K2IndexMap e : K₂(I,R) →* K₂(J,R)`, and in particular the stabilization `K2Stab n R : K₂(n,R) →* K₂(n+1,R)`.

It also records functoriality (`ringMap_id`, `ringMap_comp`, `indexMap_refl`, `indexMap_trans`) and the fact
that a ring map with a left inverse induces an injective map of Steinberg groups.
-/

namespace GroupApproximation
namespace BooneHigman
namespace SteinbergBasic

open SteinbergGroup ElementaryPadding

section RingMaps

variable {I R S T : Type*} [Fintype I] [DecidableEq I] [Ring R] [Ring S] [Ring T]

@[simp] theorem elementaryGroupMap_root (f : R →+* S) (i j : I) (hij : i ≠ j) (a : R) :
    elementaryGroupMap f (elementaryRoot i j hij a) = elementaryRoot i j hij (f a) := by
  apply Subtype.ext
  exact elementaryMatrixUnitMap_elementaryUnit f i j hij a

@[simp] theorem ringMap_id :
    ringMap (I := I) (RingHom.id R) = MonoidHom.id (SteinbergGroup I R) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change ringMap (RingHom.id R) (x i j hij a) = x i j hij a
  rw [ringMap_x]
  rfl

theorem ringMap_comp (g : S →+* T) (f : R →+* S) :
    ringMap (I := I) (g.comp f) = (ringMap g).comp (ringMap f) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change ringMap (g.comp f) (x i j hij a) = ringMap g (ringMap f (x i j hij a))
  rw [ringMap_x, ringMap_x, ringMap_x]
  rfl

theorem ringMap_ringMap (g : S →+* T) (f : R →+* S) (u : SteinbergGroup I R) :
    ringMap g (ringMap f u) = ringMap (g.comp f) u := by
  rw [ringMap_comp]
  rfl

/-- A ring map with a left inverse induces an injective map of Steinberg groups.  For example, the constants
`R → R[t]` split by evaluation at `0`. -/
theorem ringMap_injective_of_leftInverse (f : R →+* S) (g : S →+* R)
    (hgf : Function.LeftInverse g f) :
    Function.Injective (ringMap (I := I) f) := by
  have h : (ringMap (I := I) g).comp (ringMap f) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change ringMap g (ringMap f (x i j hij a)) = x i j hij a
    rw [ringMap_x, ringMap_x, hgf a]
  exact Function.LeftInverse.injective (g := ringMap (I := I) g) fun u ↦ DFunLike.congr_fun h u

/-- The projection `St → E` commutes with coefficient maps. -/
theorem projection_ringMap (f : R →+* S) (u : SteinbergGroup I R) :
    projection (ringMap f u) = elementaryGroupMap f (projection u) := by
  have h : (projection (I := I) (R := S)).comp (ringMap f) =
      (elementaryGroupMap f).comp projection := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change projection (ringMap f (x i j hij a)) =
      elementaryGroupMap f (projection (x i j hij a))
    rw [ringMap_x, projection_x, projection_x, elementaryGroupMap_root]
  exact DFunLike.congr_fun h u

theorem ringMap_mem_K2 (f : R →+* S) {u : SteinbergGroup I R} (hu : u ∈ K2 I R) :
    ringMap f u ∈ K2 I S := by
  rw [mem_K2_iff] at hu ⊢
  rw [projection_ringMap, hu, map_one]

theorem K2_le_comap_ringMap (f : R →+* S) :
    K2 I R ≤ (K2 I S).comap (ringMap f) :=
  fun _ hu ↦ ringMap_mem_K2 f hu

/-- The map `K₂(I,R) →* K₂(I,S)` induced by a coefficient map. -/
def K2Map (f : R →+* S) : K2 I R →* K2 I S :=
  ((ringMap f).comp (K2 I R).subtype).codRestrict (K2 I S) fun u ↦ ringMap_mem_K2 f u.2

@[simp] theorem K2Map_apply (f : R →+* S) (u : K2 I R) :
    (K2Map f u : SteinbergGroup I S) = ringMap f u := rfl

end RingMaps

section IndexMaps

variable {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Ring R]

@[simp] theorem indexMap_refl :
    indexMap (I := I) (R := R) (Function.Embedding.refl I) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change indexMap (Function.Embedding.refl I) (x i j hij a) = x i j hij a
  rw [indexMap_x]
  rfl

theorem indexMap_trans (e : I ↪ J) (e' : J ↪ K) :
    indexMap (R := R) (e.trans e') = (indexMap e').comp (indexMap e) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change indexMap (e.trans e') (x i j hij a) = indexMap e' (indexMap e (x i j hij a))
  rw [indexMap_x, indexMap_x, indexMap_x]
  rfl

/-- The projection `St → E` turns relabelling along `e` into identity padding along `e`. -/
theorem projection_indexMap (e : I ↪ J) (u : SteinbergGroup I R) :
    projection (indexMap e u) = elementaryPad e (projection u) := by
  have h : (projection (I := J) (R := R)).comp (indexMap e) =
      (elementaryPad e).comp projection := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change projection (indexMap e (x i j hij a)) =
      elementaryPad e (projection (x i j hij a))
    rw [indexMap_x, projection_x, projection_x, elementaryPad_elementaryRoot]
  exact DFunLike.congr_fun h u

theorem indexMap_mem_K2 (e : I ↪ J) {u : SteinbergGroup I R} (hu : u ∈ K2 I R) :
    indexMap e u ∈ K2 J R := by
  rw [mem_K2_iff] at hu ⊢
  rw [projection_indexMap, hu, map_one]

/-- The map `K₂(I,R) →* K₂(J,R)` induced by an index embedding. -/
def K2IndexMap (e : I ↪ J) : K2 I R →* K2 J R :=
  ((indexMap e).comp (K2 I R).subtype).codRestrict (K2 J R) fun u ↦ indexMap_mem_K2 e u.2

@[simp] theorem K2IndexMap_apply (e : I ↪ J) (u : K2 I R) :
    (K2IndexMap e u : SteinbergGroup J R) = indexMap e u := rfl

end IndexMaps

section Stabilization

variable (n : ℕ) (R : Type*) [Ring R]

/-- The stabilization `St_n(R) →* St_{n+1}(R)`, relabelling along `Fin.castSucc`. -/
def stab : St n R →* St (n + 1) R :=
  indexMap Fin.castSuccEmb

/-- The stabilization `E_n(R) →* E_{n+1}(R)`, padding by the identity along `Fin.castSucc`. -/
noncomputable def elementaryStab :
    elementaryGroup (Fin n) R →* elementaryGroup (Fin (n + 1)) R :=
  elementaryPad Fin.castSuccEmb

/-- The stabilization `K₂(n,R) →* K₂(n+1,R)`. -/
def K2Stab : K2n n R →* K2n (n + 1) R :=
  K2IndexMap Fin.castSuccEmb

variable {n R}

@[simp] theorem stab_x (i j : Fin n) (hij : i ≠ j) (a : R) :
    stab n R (x i j hij a) =
      x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) a :=
  indexMap_x _ i j hij a

theorem projection_stab (u : St n R) :
    projection (stab n R u) = elementaryStab n R (projection u) :=
  projection_indexMap _ u

@[simp] theorem K2Stab_apply (u : K2n n R) :
    (K2Stab n R u : St (n + 1) R) = stab n R u := rfl

end Stabilization

end SteinbergBasic
end BooneHigman
end GroupApproximation
