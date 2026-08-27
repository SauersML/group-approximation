import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Abel

/-!
# Reduced permutation lattices and their semidirect products

For a transitive action `G ↷ X`, the reduced integral permutation module is

`ker (augmentation : (X →₀ ℤ) →+ ℤ)`.

This file develops the algebraic core of the augmentation-quotient construction
used for the Kun--Thom pair.  It is independent of soficity and of the
operator-algebraic input: the augmentation map is invariant, the edge
differences form a cocycle, and a finitely generated transitive action gives a
finitely generated semidirect product.
-/

namespace GroupApproximation

open scoped Pointwise

noncomputable section

universe u

variable (X : Type u)

/-- The coefficient sum on the integral permutation lattice. -/
def permutationAugmentation : (X →₀ ℤ) →+ ℤ where
  toFun f := f.sum fun _ z ↦ z
  map_zero' := by simp
  map_add' f h := by
    classical
    exact Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

@[simp] theorem permutationAugmentation_apply (f : X →₀ ℤ) :
    permutationAugmentation X f = f.sum fun _ z ↦ z := rfl

@[simp] theorem permutationAugmentation_single (x : X) (z : ℤ) :
    permutationAugmentation X (Finsupp.single x z) = z := by
  simp [permutationAugmentation]

/-- The reduced integral permutation module. -/
abbrev ReducedPermutationLattice (X : Type u) : Type u :=
  ↑(permutationAugmentation X).ker

variable {X}

/-- The difference of two vertices, regarded as an element of the reduced
permutation lattice. -/
def reducedDifference (x y : X) : ReducedPermutationLattice X :=
  ⟨Finsupp.single x (1 : ℤ) - Finsupp.single y (1 : ℤ), by
    rw [AddMonoidHom.mem_ker, map_sub]
    simp⟩

@[simp] theorem reducedDifference_coe (x y : X) :
    (reducedDifference x y : X →₀ ℤ) =
      Finsupp.single x 1 - Finsupp.single y 1 := rfl

theorem reducedDifference_ne_zero {x y : X} (hxy : x ≠ y) :
    reducedDifference x y ≠ 0 := by
  intro h
  have hx := DFunLike.congr_fun (congrArg Subtype.val h) x
  simp [reducedDifference, hxy] at hx

private theorem finsupp_sum_smul_difference (o : X) (q : X →₀ ℤ) :
    q.sum (fun x z ↦ z •
      (Finsupp.single x (1 : ℤ) - Finsupp.single o (1 : ℤ))) =
      q - Finsupp.single o (q.sum fun _ z ↦ z) := by
  simp_rw [smul_sub]
  rw [show q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ) -
      z • Finsupp.single o (1 : ℤ)) =
      q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ)) -
        q.sum (fun _ z ↦ z • Finsupp.single o (1 : ℤ)) by
    simp only [Finsupp.sum, Finset.sum_sub_distrib]]
  rw [show q.sum (fun x z ↦ z • Finsupp.single x (1 : ℤ)) = q by
    simpa only [Finsupp.smul_single_one] using Finsupp.sum_single q]
  congr 1
  simp only [Finsupp.sum, Finsupp.smul_single_one]
  exact (map_sum (Finsupp.singleAddHom o) (fun x ↦ q x) q.support).symm

/-- Every reduced vector is the finite sum of its coefficients times the
based differences. -/
theorem reduced_eq_sum_smul_difference (o : X)
    (f : ReducedPermutationLattice X) :
    f = (f : X →₀ ℤ).sum fun x z ↦ z • reducedDifference x o := by
  have h : (f : X →₀ ℤ) = (f : X →₀ ℤ).sum (fun x z ↦ z •
      (Finsupp.single x (1 : ℤ) - Finsupp.single o (1 : ℤ))) := by
    rw [finsupp_sum_smul_difference]
    rw [show (f : X →₀ ℤ).sum (fun _ z ↦ z) = 0 from f.property]
    simp
  apply Subtype.ext
  simpa [Finsupp.sum, reducedDifference] using h

section Action

variable (G : Type*) [Group G] [MulAction G X]

local instance permutationSMul : SMul G (X →₀ ℤ) := Finsupp.comapSMul
local instance permutationMulAction : MulAction G (X →₀ ℤ) :=
  Finsupp.comapMulAction
local instance permutationDistribMulAction : DistribMulAction G (X →₀ ℤ) :=
  Finsupp.comapDistribMulAction

theorem permutationAugmentation_smul (g : G) (f : X →₀ ℤ) :
    permutationAugmentation X (g • f) = permutationAugmentation X f := by
  classical
  simp only [permutationAugmentation_apply, Finsupp.comapSMul_def]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The additive permutation action on the full integral permutation lattice. -/
def permutationAddEquiv (g : G) : (X →₀ ℤ) ≃+ (X →₀ ℤ) where
  toFun f := g • f
  invFun f := g⁻¹ • f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f h := by simp

/-- The multiplicative permutation action used to form the full semidirect
product. -/
def permutationAction : G →* MulAut (Multiplicative (X →₀ ℤ)) where
  toFun g := (permutationAddEquiv G g).toMultiplicative
  map_one' := by
    ext f
    simp [permutationAddEquiv]
  map_mul' g h := by
    ext f
    simp [permutationAddEquiv, mul_smul]

/-- The full integral permutation-lattice extension associated to `G ↷ X`. -/
abbrev PermutationExtension :=
  Multiplicative (X →₀ ℤ) ⋊[permutationAction G] G

/-- Total coefficient sum on the full permutation extension.  The acting
group maps trivially, and invariance of augmentation makes this a homomorphism. -/
def permutationExtensionAugmentation :
    PermutationExtension (X := X) G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd
    (permutationAugmentation X (Multiplicative.toAdd x.left))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change permutationAugmentation X
        (Multiplicative.toAdd
          (x.left * permutationAction G x.right y.left)) =
      permutationAugmentation X (Multiplicative.toAdd x.left) +
        permutationAugmentation X (Multiplicative.toAdd y.left)
    change permutationAugmentation X
        (Multiplicative.toAdd x.left + x.right • Multiplicative.toAdd y.left) = _
    rw [map_add, permutationAugmentation_smul]

/-- The restricted additive action on the reduced permutation lattice. -/
def reducedPermutationAddEquiv (g : G) :
    ReducedPermutationLattice X ≃+ ReducedPermutationLattice X where
  toFun f := ⟨g • (f : X →₀ ℤ), by
    rw [AddMonoidHom.mem_ker, permutationAugmentation_smul]
    exact f.property⟩
  invFun f := ⟨g⁻¹ • (f : X →₀ ℤ), by
    rw [AddMonoidHom.mem_ker, permutationAugmentation_smul]
    exact f.property⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f h := by ext; simp

@[simp] theorem reducedPermutationAddEquiv_coe (g : G)
    (f : ReducedPermutationLattice X) :
    ((reducedPermutationAddEquiv G g f : ReducedPermutationLattice X) : X →₀ ℤ) =
      g • (f : X →₀ ℤ) := rfl

/-- The action on the multiplicative copy used by `SemidirectProduct`. -/
def reducedPermutationAction :
    G →* MulAut (Multiplicative (ReducedPermutationLattice X)) where
  toFun g := (reducedPermutationAddEquiv G g).toMultiplicative
  map_one' := by
    ext f
    simp [reducedPermutationAddEquiv]
  map_mul' g h := by
    ext f
    simp [reducedPermutationAddEquiv, mul_smul]

/-- Inclusion of the reduced lattice into the full integral permutation
lattice, in multiplicative notation. -/
def reducedLatticeEmbedding :
    Multiplicative (ReducedPermutationLattice X) →* Multiplicative (X →₀ ℤ) :=
  AddMonoidHom.toMultiplicative (permutationAugmentation X).ker.subtype

/-- The reduced permutation extension associated to `G ↷ X`. -/
abbrev ReducedPermutationExtension :=
  Multiplicative (ReducedPermutationLattice X) ⋊[reducedPermutationAction G] G

/-- The reduced permutation extension embeds canonically into the full
permutation extension. -/
def reducedPermutationExtensionHom :
    ReducedPermutationExtension (X := X) G →* PermutationExtension (X := X) G :=
  SemidirectProduct.map (reducedLatticeEmbedding (X := X)) (MonoidHom.id G) (by
    intro g
    ext f
    rfl)

/-- The based edge difference. -/
def orbitDifference (o : X) (g : G) : ReducedPermutationLattice X :=
  reducedDifference (g • o) o

@[simp] theorem reducedPermutationAddEquiv_difference (g : G) (x y : X) :
    reducedPermutationAddEquiv G g (reducedDifference x y) =
      reducedDifference (g • x) (g • y) := by
  apply Subtype.ext
  change Finsupp.mapDomain (g • ·)
      (Finsupp.single x (1 : ℤ) - Finsupp.single y (1 : ℤ)) =
    Finsupp.single (g • x) 1 - Finsupp.single (g • y) 1
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single]

@[simp] theorem orbitDifference_one (o : X) : orbitDifference G o 1 = 0 := by
  apply Subtype.ext
  simp [orbitDifference, reducedDifference]

/-- The edge differences form the canonical crossed homomorphism. -/
theorem orbitDifference_mul (o : X) (g h : G) :
    orbitDifference G o (g * h) =
      reducedPermutationAddEquiv G g (orbitDifference G o h) + orbitDifference G o g := by
  change reducedDifference ((g * h) • o) o =
    reducedPermutationAddEquiv G g (reducedDifference (h • o) o) +
      reducedDifference (g • o) o
  rw [reducedPermutationAddEquiv_difference, mul_smul]
  apply Subtype.ext
  change Finsupp.single (g • h • o) 1 - Finsupp.single o 1 =
    (Finsupp.single (g • h • o) 1 - Finsupp.single (g • o) 1) +
      (Finsupp.single (g • o) 1 - Finsupp.single o 1)
  abel

/-- For a transitive action, the canonical orbit differences generate the
entire reduced permutation lattice as an additive group. -/
theorem closure_range_orbitDifference [MulAction.IsPretransitive G X] (o : X) :
    AddSubgroup.closure (Set.range (orbitDifference G o)) = ⊤ := by
  apply top_unique
  intro f _
  rw [reduced_eq_sum_smul_difference o f, Finsupp.sum]
  apply sum_mem
  intro x _
  apply AddSubgroup.zsmul_mem
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G o x
  rw [← hg]
  exact AddSubgroup.subset_closure ⟨g, rfl⟩

/-- The subgroup generated by all additive action differences `g • v - v`.
Its quotient is the module of coinvariants. -/
def reducedActionDifferenceSubgroup : AddSubgroup (ReducedPermutationLattice X) :=
  AddSubgroup.closure (Set.range fun p : G × ReducedPermutationLattice X ↦
    reducedPermutationAddEquiv G p.1 p.2 - p.2)

theorem quotient_reducedPermutationAddEquiv_eq (g : G)
    (f : ReducedPermutationLattice X) :
    QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G) (reducedPermutationAddEquiv G g f) =
      QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G) f := by
  change ((reducedPermutationAddEquiv G g f : ReducedPermutationLattice X) :
      ReducedPermutationLattice X ⧸ reducedActionDifferenceSubgroup G) =
    (f : ReducedPermutationLattice X ⧸ reducedActionDifferenceSubgroup G)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure ⟨(g, f), rfl⟩

/-- The orbit cocycle becomes an ordinary homomorphism after passage to
coinvariants. -/
def orbitDifferenceCoinvariantHom (o : X) :
    G →* Multiplicative
      (ReducedPermutationLattice X ⧸ reducedActionDifferenceSubgroup G) where
  toFun g := Multiplicative.ofAdd
    (QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G) (orbitDifference G o g))
  map_one' := by
    simp [orbitDifference_one]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G)
        (orbitDifference G o (g * h)) =
      QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G) (orbitDifference G o g) +
        QuotientAddGroup.mk' (reducedActionDifferenceSubgroup G) (orbitDifference G o h)
    rw [orbitDifference_mul, map_add, quotient_reducedPermutationAddEquiv_eq]
    exact add_comm _ _

private theorem perfect_hom_eq_one {A : Type*} [Group A] [IsMulCommutative A]
    [Group.IsPerfect G] (f : G →* A) (g : G) : f g = 1 := by
  let x : f.range := ⟨f g, ⟨g, rfl⟩⟩
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  haveI : IsMulCommutative f.range := inferInstance
  haveI : Subsingleton f.range := inferInstance
  exact congrArg Subtype.val (Subsingleton.elim x 1)

/-- If the acting group is perfect and the action is transitive, its action
differences already generate the entire reduced permutation lattice.  This
is the elementary coinvariant-vanishing statement behind perfectness of the
augmentation core. -/
theorem reducedActionDifferenceSubgroup_eq_top [MulAction.IsPretransitive G X]
    [Group.IsPerfect G] (o : X) :
    reducedActionDifferenceSubgroup (X := X) G = ⊤ := by
  have horbit : Set.range (orbitDifference G o) ⊆
      reducedActionDifferenceSubgroup (X := X) G := by
    rintro _ ⟨g, rfl⟩
    have h := perfect_hom_eq_one G (orbitDifferenceCoinvariantHom G o) g
    change Multiplicative.ofAdd
        (QuotientAddGroup.mk' (reducedActionDifferenceSubgroup (X := X) G)
          (orbitDifference G o g)) = Multiplicative.ofAdd 0 at h
    have hzero := Multiplicative.ofAdd.injective h
    exact (QuotientAddGroup.eq_zero_iff
      (N := reducedActionDifferenceSubgroup (X := X) G) (orbitDifference G o g)).mp hzero
  apply top_unique
  rw [← closure_range_orbitDifference G o]
  exact (AddSubgroup.closure_le _).mpr horbit

open scoped commutatorElement

/-- An additive action difference is literally a commutator in the reduced
permutation semidirect product. -/
theorem inl_actionDifference_eq_commutator (g : G)
    (f : ReducedPermutationLattice X) :
    SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G)
        (Multiplicative.ofAdd
          (reducedPermutationAddEquiv G g f - f)) =
      ⁅SemidirectProduct.inr (N := Multiplicative (ReducedPermutationLattice X))
          (φ := reducedPermutationAction G) g,
        SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G)
          (Multiplicative.ofAdd f)⁆ := by
  have hmul : Multiplicative.ofAdd (reducedPermutationAddEquiv G g f - f) =
      reducedPermutationAction G g (Multiplicative.ofAdd f) *
        (Multiplicative.ofAdd f)⁻¹ := by
    apply Multiplicative.toAdd.injective
    simp [reducedPermutationAction, sub_eq_add_neg]
  rw [hmul]
  rw [map_mul, SemidirectProduct.inl_aut, map_inv]
  simp [commutatorElement_def, mul_assoc]

/-- The additive vectors whose lamp embeddings lie in the commutator subgroup
of the reduced permutation extension. -/
def inlCommutatorPreimage : AddSubgroup (ReducedPermutationLattice X) :=
  ((commutator (ReducedPermutationExtension (X := X) G)).comap
    (SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G))).toAddSubgroup

theorem actionDifference_mem_inlCommutatorPreimage (g : G)
    (f : ReducedPermutationLattice X) :
    reducedPermutationAddEquiv G g f - f ∈ inlCommutatorPreimage (X := X) G := by
  change SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G)
      (Multiplicative.ofAdd (reducedPermutationAddEquiv G g f - f)) ∈
        commutator (ReducedPermutationExtension (X := X) G)
  rw [inl_actionDifference_eq_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- For a nonempty transitive action of a perfect group, every reduced lamp
lies in the commutator subgroup of the associated semidirect product. -/
theorem inl_mem_commutator (hX : Nonempty X) [MulAction.IsPretransitive G X]
    [Group.IsPerfect G] (f : ReducedPermutationLattice X) :
    SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G)
        (Multiplicative.ofAdd f) ∈
      commutator (ReducedPermutationExtension (X := X) G) := by
  letI : Nonempty X := hX
  change f ∈ inlCommutatorPreimage (X := X) G
  have hle : reducedActionDifferenceSubgroup (X := X) G ≤
      inlCommutatorPreimage (X := X) G := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact actionDifference_mem_inlCommutatorPreimage G g v
  let o : X := Classical.choice inferInstance
  rw [reducedActionDifferenceSubgroup_eq_top G o] at hle
  exact hle (AddSubgroup.mem_top f)

/-- The acting copy of a perfect group lies in the commutator subgroup of
every semidirect product. -/
theorem inr_mem_commutator [Group.IsPerfect G] (g : G) :
    SemidirectProduct.inr (N := Multiplicative (ReducedPermutationLattice X))
        (φ := reducedPermutationAction G) g ∈
      commutator (ReducedPermutationExtension (X := X) G) := by
  have hg : g ∈ commutator G := Group.IsPerfect.mem_commutator
  have hmap := Subgroup.mem_map_of_mem
    (SemidirectProduct.inr (N := Multiplicative (ReducedPermutationLattice X))
      (φ := reducedPermutationAction G)) hg
  rw [_root_.commutator_def, Subgroup.map_commutator] at hmap
  exact Subgroup.commutator_mono le_top le_top hmap

/-- A perfect group acting transitively on a nonempty set has a perfect
reduced integral permutation-lattice extension. -/
theorem reducedPermutationExtension_isPerfect (hX : Nonempty X)
    [MulAction.IsPretransitive G X] [Group.IsPerfect G] :
    Group.IsPerfect (ReducedPermutationExtension (X := X) G) := by
  letI : Nonempty X := hX
  rw [Group.isPerfect_def, eq_top_iff]
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact Subgroup.mul_mem _
    (by simpa using inl_mem_commutator G hX (Multiplicative.toAdd x.left))
    (inr_mem_commutator G x.right)

/-- The canonical image of the reduced extension lies in the commutator
subgroup of the full permutation extension. -/
theorem reducedPermutationExtensionHom_mem_commutator (hX : Nonempty X)
    [MulAction.IsPretransitive G X] [Group.IsPerfect G]
    (x : ReducedPermutationExtension (X := X) G) :
    reducedPermutationExtensionHom (X := X) G x ∈
      commutator (PermutationExtension (X := X) G) := by
  letI : Nonempty X := hX
  letI : Group.IsPerfect (ReducedPermutationExtension (X := X) G) :=
    reducedPermutationExtension_isPerfect G hX
  have hx : x ∈ commutator (ReducedPermutationExtension (X := X) G) :=
    Group.IsPerfect.mem_commutator
  have hmap := Subgroup.mem_map_of_mem
    (reducedPermutationExtensionHom (X := X) G) hx
  rw [_root_.commutator_def, Subgroup.map_commutator] at hmap
  exact Subgroup.commutator_mono le_top le_top hmap

/-- The canonical reduced extension is precisely the augmentation kernel in
the full permutation extension. -/
theorem reducedPermutationExtensionHom_range_eq_augmentation_ker :
    (reducedPermutationExtensionHom (X := X) G).range =
      (permutationExtensionAugmentation (X := X) G).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change permutationAugmentation X (x.left.toAdd : X →₀ ℤ) = 0
    exact x.left.toAdd.property
  · intro x hx
    have hsum : permutationAugmentation X (Multiplicative.toAdd x.left) = 0 := by
      have h := MonoidHom.mem_ker.mp hx
      change Multiplicative.ofAdd
          (permutationAugmentation X (Multiplicative.toAdd x.left)) =
        Multiplicative.ofAdd 0 at h
      exact Multiplicative.ofAdd.injective h
    let f : ReducedPermutationLattice X := ⟨Multiplicative.toAdd x.left, hsum⟩
    refine ⟨⟨Multiplicative.ofAdd f, x.right⟩, ?_⟩
    ext <;> rfl

/-- For a perfect group acting transitively, the derived subgroup of the full
integral permutation extension is exactly the augmentation-kernel extension. -/
theorem permutationExtension_commutator_eq_augmentation_ker (hX : Nonempty X)
    [MulAction.IsPretransitive G X] [Group.IsPerfect G] :
    commutator (PermutationExtension (X := X) G) =
      (permutationExtensionAugmentation (X := X) G).ker := by
  letI : Nonempty X := hX
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker _
  · intro x hx
    have hsum : permutationAugmentation X (Multiplicative.toAdd x.left) = 0 := by
      have h := MonoidHom.mem_ker.mp hx
      change Multiplicative.ofAdd
          (permutationAugmentation X (Multiplicative.toAdd x.left)) =
        Multiplicative.ofAdd 0 at h
      exact Multiplicative.ofAdd.injective h
    let f : ReducedPermutationLattice X := ⟨Multiplicative.toAdd x.left, hsum⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    apply Subgroup.mul_mem
    · have h := reducedPermutationExtensionHom_mem_commutator G hX
          (SemidirectProduct.inl (G := G) (φ := reducedPermutationAction G)
            (Multiplicative.ofAdd f))
      simpa [reducedPermutationExtensionHom, reducedLatticeEmbedding, f] using h
    · have h := reducedPermutationExtensionHom_mem_commutator G hX
          (SemidirectProduct.inr
            (N := Multiplicative (ReducedPermutationLattice X))
            (φ := reducedPermutationAction G) x.right)
      simpa [reducedPermutationExtensionHom] using h

end Action

end

end GroupApproximation
