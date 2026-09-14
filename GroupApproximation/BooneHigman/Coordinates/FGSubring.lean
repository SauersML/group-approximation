import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# A finitely generated linear group has entries in a finitely generated subring

Let `ρ : G →* GL_n(K)` with `G` finitely generated.  The entries of the images of a finite
generating set and of their inverses form a finite set `s ⊆ K`.  Every subring `B ⊇ s` carries the
whole image: the units of `M_n(K)` whose entries and inverse entries lie in `B` form a subgroup
(`glEntriesIn B`), and each of them lifts to `GL_n(B)` (`liftGL`).

* `exists_finset_factor`: some finite `s ⊆ K` works for every subring `B ⊇ s`, with
  `GL.map B.subtype ∘ ρ' = ρ`.
* `factor_injective`: the factor `ρ'` is injective when `ρ` is.
-/

namespace GroupApproximation.BooneHigman.Coordinates

open Matrix

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Units of `M_n(K)` whose entries, and the entries of whose inverse, lie in `B`. -/
def glEntriesIn (B : Subring K) : Subgroup (GL n K) where
  carrier := {u | ∀ i j, (u : Matrix n n K) i j ∈ B ∧ ((u⁻¹ : GL n K) : Matrix n n K) i j ∈ B}
  one_mem' := by
    simp only [Set.mem_setOf_eq, inv_one, Units.val_one]
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact ⟨one_mem B, one_mem B⟩
    · exact ⟨zero_mem B, zero_mem B⟩
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hu i k).1 (hv k j).1
    · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hv i k).2 (hu k j).2
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq, inv_inv] at hu ⊢
    exact fun i j => ⟨(hu i j).2, (hu i j).1⟩

theorem mem_glEntriesIn {B : Subring K} {u : GL n K} :
    u ∈ glEntriesIn B ↔
      ∀ i j, (u : Matrix n n K) i j ∈ B ∧ ((u⁻¹ : GL n K) : Matrix n n K) i j ∈ B :=
  Iff.rfl

/-- A matrix over `K` with entries in `B`, viewed over `B`. -/
def subtypeMatrix {B : Subring K} (M : Matrix n n K) (hM : ∀ i j, M i j ∈ B) : Matrix n n B :=
  Matrix.of fun i j => ⟨M i j, hM i j⟩

theorem mapMatrix_subtypeMatrix {B : Subring K} (M : Matrix n n K) (hM : ∀ i j, M i j ∈ B) :
    B.subtype.mapMatrix (subtypeMatrix M hM) = M := by
  ext i j
  rfl

theorem mul_eq_one_of_mapMatrix {B : Subring K} {M M' : Matrix n n B}
    (h : B.subtype.mapMatrix M * B.subtype.mapMatrix M' = 1) : M * M' = 1 := by
  have hinj : Function.Injective (B.subtype.mapMatrix (m := n)) :=
    Matrix.map_injective Subtype.val_injective
  apply hinj
  rw [map_mul, map_one]
  exact h

/-- An element of `glEntriesIn B`, viewed in `GL_n(B)`. -/
def liftGL (B : Subring K) (u : GL n K) (hu : u ∈ glEntriesIn B) : GL n B where
  val := subtypeMatrix (u : Matrix n n K) fun i j => (mem_glEntriesIn.1 hu i j).1
  inv := subtypeMatrix ((u⁻¹ : GL n K) : Matrix n n K) fun i j => (mem_glEntriesIn.1 hu i j).2
  val_inv := mul_eq_one_of_mapMatrix (by
    rw [mapMatrix_subtypeMatrix, mapMatrix_subtypeMatrix]
    exact u.mul_inv)
  inv_val := mul_eq_one_of_mapMatrix (by
    rw [mapMatrix_subtypeMatrix, mapMatrix_subtypeMatrix]
    exact u.inv_mul)

theorem glMap_liftGL (B : Subring K) (u : GL n K) (hu : u ∈ glEntriesIn B) :
    Matrix.GeneralLinearGroup.map B.subtype (liftGL B u hu) = u :=
  Units.ext (mapMatrix_subtypeMatrix _ _)

/-- **Entries in a finitely generated subring.**  For a finitely generated group `G` and
`ρ : G →* GL_n(K)` there is a finite set `s ⊆ K` such that `ρ` factors through `GL_n(B)` for every
subring `B ⊇ s`. -/
theorem exists_finset_factor {G : Type*} [Group G] [hG : Group.FG G] (ρ : G →* GL n K) :
    ∃ s : Finset K, ∀ B : Subring K, (↑s : Set K) ⊆ B →
      ∃ ρ' : G →* GL n B, (Matrix.GeneralLinearGroup.map B.subtype).comp ρ' = ρ := by
  classical
  obtain ⟨T, hT⟩ := hG.out
  let s : Finset K := T.biUnion fun g =>
    Finset.univ.image (fun ij : n × n => (ρ g : Matrix n n K) ij.1 ij.2) ∪
      Finset.univ.image (fun ij : n × n => (((ρ g)⁻¹ : GL n K) : Matrix n n K) ij.1 ij.2)
  refine ⟨s, fun B hB => ?_⟩
  have hle : Subgroup.closure (T : Set G) ≤ (glEntriesIn B).comap ρ := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_glEntriesIn]
    intro i j
    refine ⟨hB ?_, hB ?_⟩
    · exact Finset.mem_biUnion.2
        ⟨t, ht, Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)⟩
    · exact Finset.mem_biUnion.2
        ⟨t, ht, Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)⟩
  have hmem : ∀ g, ρ g ∈ glEntriesIn B := fun g =>
    hle (hT ▸ Subgroup.mem_top g : g ∈ Subgroup.closure (T : Set G))
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := n) B.subtype) :=
    glMap_injective Subtype.val_injective
  refine ⟨{ toFun := fun g => liftGL B (ρ g) (hmem g), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show liftGL B (ρ 1) (hmem 1) = 1
    apply hinj
    rw [glMap_liftGL, map_one, map_one]
  · intro g h
    show liftGL B (ρ (g * h)) (hmem (g * h)) = liftGL B (ρ g) (hmem g) * liftGL B (ρ h) (hmem h)
    apply hinj
    rw [glMap_liftGL, map_mul (Matrix.GeneralLinearGroup.map B.subtype), glMap_liftGL,
      glMap_liftGL, map_mul ρ]
  · ext g : 1
    exact glMap_liftGL B (ρ g) (hmem g)

/-- The factor through `GL_n(B)` is injective when `ρ` is. -/
theorem factor_injective {G : Type*} [Group G] {B : Subring K} {ρ : G →* GL n K}
    {ρ' : G →* GL n B} (h : (Matrix.GeneralLinearGroup.map B.subtype).comp ρ' = ρ)
    (hρ : Function.Injective ρ) : Function.Injective ρ' := by
  intro x y hxy
  apply hρ
  rw [← h, MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]

end GroupApproximation.BooneHigman.Coordinates
