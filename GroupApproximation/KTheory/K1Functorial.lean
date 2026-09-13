import GroupApproximation.Analysis.CStarKOne

/-!
# Functoriality of `K_1`

`Analysis/CStarKOne` builds topological `K_1(A)` of a unital C⋆-algebra as the colimit of the
groups `U(M_n(A))/U_0(M_n(A))` along the block inclusions `u ↦ diag (u, 1)`, and
`Analysis/CStarKOneWhitehead` shows that it is abelian.  This file makes `K_1` a functor on unital
⋆-homomorphisms.

* `GroupTower.colimMap`: homomorphisms between the levels of two towers which commute with the
  transition maps induce a homomorphism of the colimits.
* `matMapHom φ n`: entrywise application of `φ : A →⋆ₐ[ℂ] B` to `n × n` matrices, a continuous
  star monoid homomorphism commuting with the block inclusions.
* `KOne.map φ : KOne A →* KOne B`, with `KOne.map_id` and `KOne.map_comp`.
-/

namespace GroupApproximation

universe u v w

noncomputable section

namespace GroupTower

variable {G : ℕ → Type u} {H : ℕ → Type v} [∀ n, Group (G n)] [∀ n, Group (H n)]
  (T : GroupTower G) (S : GroupTower H)

/-- The function between colimits induced by level maps commuting with the transition maps. -/
def colimLift (f : ∀ n, G n →* H n)
    (hf : ∀ {n m : ℕ} (h : n ≤ m) (x : G n), f m (T.map h x) = S.map h (f n x)) :
    T.Colim → S.Colim :=
  Quotient.lift (fun x : Σ n, G n => S.mkAt x.1 (f x.1 x.2)) fun a b hab => by
    obtain ⟨k, hx, hy, e⟩ := hab
    exact S.mkAt_eq_mkAt hx hy
      ((hf hx a.2).symm.trans ((congrArg (f k) e).trans (hf hy b.2)))

variable {T S}

@[simp] theorem colimLift_mkAt (f : ∀ n, G n →* H n)
    (hf : ∀ {n m : ℕ} (h : n ≤ m) (x : G n), f m (T.map h x) = S.map h (f n x))
    (n : ℕ) (x : G n) : colimLift T S f hf (T.mkAt n x) = S.mkAt n (f n x) := rfl

variable (T S)

/-- **The colimit of a morphism of towers.**  Level homomorphisms commuting with the transition
maps induce a homomorphism between the colimits. -/
def colimMap (f : ∀ n, G n →* H n)
    (hf : ∀ {n m : ℕ} (h : n ≤ m) (x : G n), f m (T.map h x) = S.map h (f n x)) :
    T.Colim →* S.Colim where
  toFun := colimLift T S f hf
  map_one' := by
    show S.mkAt 0 (f 0 1) = S.mkAt 0 1
    rw [map_one]
  map_mul' a b := by
    obtain ⟨n, x, rfl⟩ := T.exists_mkAt a
    obtain ⟨m, y, rfl⟩ := T.exists_mkAt b
    rw [T.mkAt_mul_mkAt x y (le_max_left n m) (le_max_right n m)]
    simp only [colimLift_mkAt]
    rw [map_mul, hf (le_max_left n m) x, hf (le_max_right n m) y,
      S.mkAt_mul_mkAt (f n x) (f m y) (le_max_left n m) (le_max_right n m)]

@[simp] theorem colimMap_mkAt (f : ∀ n, G n →* H n)
    (hf : ∀ {n m : ℕ} (h : n ≤ m) (x : G n), f m (T.map h x) = S.map h (f n x))
    (n : ℕ) (x : G n) : colimMap T S f hf (T.mkAt n x) = S.mkAt n (f n x) := rfl

theorem colimMap_iota (f : ∀ n, G n →* H n)
    (hf : ∀ {n m : ℕ} (h : n ≤ m) (x : G n), f m (T.map h x) = S.map h (f n x))
    (n : ℕ) (x : G n) : colimMap T S f hf (T.iota n x) = S.iota n (f n x) := rfl

end GroupTower

section Matrices

variable {A : Type u} {B : Type v} {C : Type w} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- Entrywise application of `φ` to a square matrix. -/
def matMap (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (M : CStarMat n A) : CStarMat n B := fun i j => φ (M i j)

theorem matMap_apply (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (M : CStarMat n A) (i j : Fin n) :
    matMap φ n M i j = φ (M i j) := rfl

def matMapHom (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : CStarMat n A →⋆* CStarMat n B where
  toFun := matMap φ n
  map_one' := by
    ext i j
    show matMap φ n 1 i j = (1 : CStarMat n B) i j
    rw [matMap_apply, CStarMatrix.one_apply, CStarMatrix.one_apply]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  map_mul' M N := by
    ext i j
    show matMap φ n (M * N) i j = (matMap φ n M * matMap φ n N) i j
    rw [matMap_apply, CStarMatrix.mul_apply, CStarMatrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_mul φ (M i l) (N l j)
  map_star' M := by
    ext i j
    show matMap φ n (star M) i j = (star (matMap φ n M)) i j
    rw [matMap_apply, CStarMatrix.star_apply, CStarMatrix.star_apply, matMap_apply]
    exact map_star φ (M j i)

@[simp] theorem matMapHom_apply (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (M : CStarMat n A) (i j : Fin n) :
    matMapHom φ n M i j = φ (M i j) := rfl

/-- Entrywise application commutes with the block inclusion `M ↦ diag (M, 1)`. -/
theorem matMapHom_blockOne (φ : A →⋆ₐ[ℂ] B) {n : ℕ} (M : CStarMat n A) (m : ℕ) :
    matMapHom φ m (blockOne M m) = blockOne (matMapHom φ n M) m := by
  ext i j
  rw [matMapHom_apply]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt M i j hi hj,
        blockOne_apply_of_lt_of_lt (matMapHom φ n M) i j hi hj, matMapHom_apply]
    · rw [blockOne_apply_of_lt_of_not_lt M i j hi hj,
        blockOne_apply_of_lt_of_not_lt (matMapHom φ n M) i j hi hj, map_zero]
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_not_lt_of_lt M i j hi hj,
        blockOne_apply_of_not_lt_of_lt (matMapHom φ n M) i j hi hj, map_zero]
    · rw [blockOne_apply_of_not_lt_of_not_lt M i j hi hj,
        blockOne_apply_of_not_lt_of_not_lt (matMapHom φ n M) i j hi hj]
      split_ifs
      · exact map_one φ
      · exact map_zero φ

/-- Entrywise application to unitary matrices. -/
def matMapUnitary (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : unitary (CStarMat n A) →* unitary (CStarMat n B) :=
  (Unitary.map (matMapHom φ n)).toMonoidHom

@[simp] theorem coe_matMapUnitary (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (v : unitary (CStarMat n A)) :
    ((matMapUnitary φ n v : unitary (CStarMat n B)) : CStarMat n B)
      = matMapHom φ n (v : CStarMat n A) := rfl

/-- A unital ⋆-homomorphism between C⋆-algebras is contractive, hence continuous, and so is its
entrywise application to matrices. -/
theorem continuous_matMapHom (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : Continuous (matMapHom φ n) := by
  have hφ : Continuous φ := AddMonoidHomClass.continuous_of_bound φ 1 fun a => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ a
  refine continuous_matrix fun i j => ?_
  exact (hφ.comp (continuous_apply_apply i j)).congr fun M => (matMapHom_apply φ n M i j).symm

theorem continuous_matMapUnitary (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : Continuous (matMapUnitary φ n) :=
  continuous_induced_rng.mpr ((continuous_matMapHom φ n).comp continuous_subtype_val)

section Order

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

/-- The map `U(M_n(A))/U_0(M_n(A)) → U(M_n(B))/U_0(M_n(B))` induced by `φ`. -/
def kOneLevelMap (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : KOneLevel A n →* KOneLevel B n :=
  unitaryClassMap (matMapUnitary φ n) (continuous_matMapUnitary φ n)

@[simp] theorem kOneLevelMap_mk (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (v : unitary (CStarMat n A)) :
    kOneLevelMap φ n (QuotientGroup.mk v) = QuotientGroup.mk (matMapUnitary φ n v) := rfl

theorem kOneLevelMap_kOneMap (φ : A →⋆ₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (x : KOneLevel A n) :
    kOneLevelMap φ m (kOneMap A h x) = kOneMap B h (kOneLevelMap φ n x) := by
  refine QuotientGroup.induction_on x fun v => ?_
  show (QuotientGroup.mk (matMapUnitary φ m (blockOneUnitary h v)) : KOneLevel B m)
    = QuotientGroup.mk (blockOneUnitary h (matMapUnitary φ n v))
  rw [show matMapUnitary φ m (blockOneUnitary h v) = blockOneUnitary h (matMapUnitary φ n v) from
    Subtype.ext (matMapHom_blockOne φ (v : CStarMat n A) m)]

namespace KOne

/-- **Functoriality of `K_1`**: a unital ⋆-homomorphism `φ : A →⋆ₐ[ℂ] B` induces
`K_1(A) →* K_1(B)`, entrywise on unitary matrices. -/
def map (φ : A →⋆ₐ[ℂ] B) : KOne A →* KOne B :=
  GroupTower.colimMap (kOneTower A) (kOneTower B) (fun n => kOneLevelMap φ n)
    fun h x => kOneLevelMap_kOneMap φ h x

@[simp] theorem map_iota (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (x : KOneLevel A n) :
    map φ (kOneIota A n x) = kOneIota B n (kOneLevelMap φ n x) := rfl

theorem map_iota_mk (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (v : unitary (CStarMat n A)) :
    map φ (kOneIota A n (QuotientGroup.mk v))
      = kOneIota B n (QuotientGroup.mk (matMapUnitary φ n v)) := rfl

theorem map_id : map (StarAlgHom.id ℂ A) = MonoidHom.id (KOne A) := by
  refine MonoidHom.ext fun a => ?_
  obtain ⟨n, x, rfl⟩ := (kOneTower A).exists_iota a
  refine QuotientGroup.induction_on x fun v => ?_
  rw [MonoidHom.id_apply]
  show kOneIota A n (QuotientGroup.mk (matMapUnitary (StarAlgHom.id ℂ A) n v))
    = kOneIota A n (QuotientGroup.mk v)
  rw [show matMapUnitary (StarAlgHom.id ℂ A) n v = v from
    Subtype.ext (CStarMatrix.ext fun i j => rfl)]

theorem map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  refine MonoidHom.ext fun a => ?_
  obtain ⟨n, x, rfl⟩ := (kOneTower A).exists_iota a
  refine QuotientGroup.induction_on x fun v => ?_
  rw [MonoidHom.comp_apply]
  show kOneIota C n (QuotientGroup.mk (matMapUnitary (ψ.comp φ) n v))
    = kOneIota C n (QuotientGroup.mk (matMapUnitary ψ n (matMapUnitary φ n v)))
  rw [show matMapUnitary (ψ.comp φ) n v = matMapUnitary ψ n (matMapUnitary φ n v) from
    Subtype.ext (CStarMatrix.ext fun i j => rfl)]

end KOne

end Order

end Matrices

end

end GroupApproximation
