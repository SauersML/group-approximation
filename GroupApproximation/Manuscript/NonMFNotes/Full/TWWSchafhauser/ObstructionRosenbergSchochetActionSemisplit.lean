import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetComap

/-!
# The semisplit extension group `Ext⁻¹(S, J) = KK¹(S, J)`

Lane `TWWSch3d3-3A`, work order `WO-TWWSchafhauser-3d3-3A`. The manuscript statement is
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). It cites
Tikuisis--White--Winter through C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.

The `KK`-action on `Ext(-, J)` is built in the Cuntz picture `KK(A, B) = [𝒦 ⊗ qA, 𝒦 ⊗ qB]`.
The algebra `qA` is not nuclear. The Busby-picture group `ExtGroup (qA) J` is therefore not
`KK¹(qA, J)`, and it is not known to be homotopy invariant. On the Cuntz side we use Kasparov's
group `Ext⁻¹` of **semisplit** extensions (G. G. Kasparov, *The operator K-functor and extensions
of C⋆-algebras*, Izv. Akad. Nauk SSSR 44 (1980), §7). An extension is semisplit when its Busby
map has a completely positive lift. For separable `S` this group is `KK¹(S, J)`.

* `IsCPLift ψ`: `ψ : S → 𝓛(H_J)` is linear, bounded and completely positive. Complete
  positivity is stated in kernel form: `∑ᵢⱼ ⟪vᵢ, ψ(aᵢ⋆ aⱼ) vⱼ⟫ ≥ 0` in `J`.
* `BusbyCycle.IsSemisplit`: the cycle agrees modulo compacts with a completely positive lift.
* `ExtSS S J`: semisplit cycles modulo split cycles, unitary equivalence and direct sums. The
  relations are those of `ExtGroup`.
* `ExtSS.comap`: contravariant functoriality, with `comap_id` and `comap_comp`.
* `ExtSS.toExt : ExtSS S J →+ ExtGroup S J`, which is natural. If every Busby cycle of `S` is
  semisplit, it is bijective (`toExt_bijective_of_forall_isSemisplit`). By the Choi--Effros
  lifting theorem this is the case for nuclear separable `S`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Semisplit

variable {S T U : Type} [NonUnitalCStarAlgebra S] [NonUnitalCStarAlgebra T]
  [NonUnitalCStarAlgebra U]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- `ψ : S → 𝓛(H_J)` is a **completely positive lift**. It is pointwise bounded, additive and
`ℂ`-linear, and completely positive in kernel form: for all `a₁, …, aₙ ∈ S` and
`v₁, …, vₙ ∈ H_J` we have `∑ᵢⱼ ⟪vᵢ, ψ(aᵢ⋆ aⱼ) vⱼ⟫ ≥ 0` in `J` (E. C. Lance, *Hilbert
C⋆-modules*, LMS Lecture Notes 210, Ch. 5). -/
structure IsCPLift (ψ : S → StdOp J) : Prop where
  /-- Every operator in the image is bounded. -/
  bounded : ∀ a : S, Adjointable.IsBounded (ψ a)
  /-- `ψ` is additive. -/
  map_add : ∀ (a a' : S) (v : (standardModule ℕ J).carrier),
    (ψ (a + a')).toFun v = (ψ a).toFun v + (ψ a').toFun v
  /-- `ψ` is `ℂ`-linear. -/
  map_smul : ∀ (c : ℂ) (a : S) (v : (standardModule ℕ J).carrier),
    (ψ (c • a)).toFun v = c • (ψ a).toFun v
  /-- `ψ` is completely positive (kernel form). -/
  positive : ∀ (n : ℕ) (a : Fin n → S) (v : Fin n → (standardModule ℕ J).carrier),
    0 ≤ ∑ i, ∑ j, (standardModule ℕ J).inner (v i) ((ψ (star (a i) * a j)).toFun (v j))

/-- A completely positive lift composed with a `⋆`-homomorphism is a completely positive lift. -/
theorem IsCPLift.comp (f : S →⋆ₙₐ[ℂ] T) {ψ : T → StdOp J} (hψ : IsCPLift ψ) :
    IsCPLift (fun a : S => ψ (f a)) where
  bounded a := hψ.bounded (f a)
  map_add a a' v := by
    show (ψ (f (a + a'))).toFun v = (ψ (f a)).toFun v + (ψ (f a')).toFun v
    rw [_root_.map_add]
    exact hψ.map_add (f a) (f a') v
  map_smul c a v := by
    show (ψ (f (c • a))).toFun v = c • (ψ (f a)).toFun v
    rw [_root_.map_smul]
    exact hψ.map_smul c (f a) v
  positive n a v := by
    have e : ∀ i j : Fin n, f (star (a i) * a j) = star (f (a i)) * f (a j) := fun i j => by
      rw [_root_.map_mul, _root_.map_star]
    show 0 ≤ ∑ i, ∑ j,
      (standardModule ℕ J).inner (v i) ((ψ (f (star (a i) * a j))).toFun (v j))
    simp only [e]
    exact hψ.positive n (fun i => f (a i)) v

/-- A Busby cycle is **semisplit** when it agrees modulo compacts with a completely positive lift.
Equivalently, the extension has a completely positive splitting (Kasparov 1980, §7). -/
def BusbyCycle.IsSemisplit (x : BusbyCycle S J) : Prop :=
  ∃ ψ : S → StdOp J, IsCPLift ψ ∧ ∀ a : S, CompactEq J (x.lift a) (ψ a)

/-- Pulling back a semisplit cycle gives a semisplit cycle. -/
theorem BusbyCycle.IsSemisplit.comap (f : S →⋆ₙₐ[ℂ] T) {x : BusbyCycle T J}
    (hx : x.IsSemisplit) : (x.comap f).IsSemisplit := by
  obtain ⟨ψ, hψ, hxψ⟩ := hx
  exact ⟨fun a => ψ (f a), hψ.comp f, fun a => hxψ (f a)⟩

variable (S J)

/-- Semisplit Busby cycles. -/
abbrev SSCycle : Type :=
  {x : BusbyCycle S J // x.IsSemisplit}

/-- The generating relations of `ExtSS S J`. They are the relations of `ExtGroup`, restricted to
semisplit cycles. -/
def ssGenerators : Set (FreeAbelianGroup (SSCycle S J)) :=
  {r | (∃ x : SSCycle S J, x.1.IsSplit ∧ r = FreeAbelianGroup.of x) ∨
    (∃ x y : SSCycle S J, x.1.IsUnitarilyEquivalent y.1 ∧
      r = FreeAbelianGroup.of x - FreeAbelianGroup.of y) ∨
    (∃ z x y : SSCycle S J, z.1.IsDirectSum x.1 y.1 ∧
      r = FreeAbelianGroup.of z - (FreeAbelianGroup.of x + FreeAbelianGroup.of y))}

/-- The subgroup generated by the relations. -/
def ssRelations : AddSubgroup (FreeAbelianGroup (SSCycle S J)) :=
  AddSubgroup.closure (ssGenerators S J)

/-- **`Ext⁻¹(S, J)`**: semisplit Busby cycles modulo split cycles, unitary equivalence and direct
sums. -/
abbrev ExtSS : Type :=
  FreeAbelianGroup (SSCycle S J) ⧸ ssRelations S J

variable {S J}

/-- The class of a semisplit cycle. -/
def ExtSS.mk (x : SSCycle S J) : ExtSS S J :=
  ((FreeAbelianGroup.of x : FreeAbelianGroup (SSCycle S J)) : ExtSS S J)

/-- A split cycle has class `0`. -/
theorem ExtSS.mk_eq_zero_of_isSplit {x : SSCycle S J} (hx : x.1.IsSplit) : ExtSS.mk x = 0 := by
  show ((FreeAbelianGroup.of x : FreeAbelianGroup (SSCycle S J)) : ExtSS S J) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of x ∈ ssGenerators S J from Or.inl ⟨x, hx, rfl⟩)

/-- Unitarily equivalent cycles have the same class. -/
theorem ExtSS.mk_eq_of_isUnitarilyEquivalent {x y : SSCycle S J}
    (h : x.1.IsUnitarilyEquivalent y.1) : ExtSS.mk x = ExtSS.mk y := by
  show ((FreeAbelianGroup.of x : FreeAbelianGroup (SSCycle S J)) : ExtSS S J) =
    ((FreeAbelianGroup.of y : FreeAbelianGroup (SSCycle S J)) : ExtSS S J)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of x - FreeAbelianGroup.of y ∈ ssGenerators S J from
      Or.inr (Or.inl ⟨x, y, h, rfl⟩))

/-- The class of a direct sum is the sum of the classes. -/
theorem ExtSS.mk_eq_add_of_isDirectSum {z x y : SSCycle S J} (h : z.1.IsDirectSum x.1 y.1) :
    ExtSS.mk z = ExtSS.mk x + ExtSS.mk y := by
  show ((FreeAbelianGroup.of z : FreeAbelianGroup (SSCycle S J)) : ExtSS S J) =
    ((FreeAbelianGroup.of x : FreeAbelianGroup (SSCycle S J)) : ExtSS S J) +
      ((FreeAbelianGroup.of y : FreeAbelianGroup (SSCycle S J)) : ExtSS S J)
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of z - (FreeAbelianGroup.of x + FreeAbelianGroup.of y) ∈
      ssGenerators S J from Or.inr (Or.inr ⟨z, x, y, h, rfl⟩))

variable (S J)

/-- An assignment of values to semisplit cycles that respects the relations of `ExtSS S J`. -/
structure ExtSS.Respecting (G : Type*) [AddCommGroup G] where
  /-- The value on a cycle. -/
  toFun : SSCycle S J → G
  /-- Split cycles go to `0`. -/
  map_split : ∀ x : SSCycle S J, x.1.IsSplit → toFun x = 0
  /-- Unitarily equivalent cycles have equal values. -/
  map_unitary : ∀ x y : SSCycle S J, x.1.IsUnitarilyEquivalent y.1 → toFun x = toFun y
  /-- Direct sums are additive. -/
  map_sum : ∀ z x y : SSCycle S J, z.1.IsDirectSum x.1 y.1 → toFun z = toFun x + toFun y

variable {S J}

theorem ExtSS.ssRelations_le_ker {G : Type*} [AddCommGroup G] (f : ExtSS.Respecting S J G) :
    ssRelations S J ≤ (FreeAbelianGroup.lift f.toFun).ker := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro r (⟨x, hx, rfl⟩ | ⟨x, y, h, rfl⟩ | ⟨z, x, y, h, rfl⟩)
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [FreeAbelianGroup.lift_apply_of]
    exact f.map_split x hx
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      f.map_unitary x y h, sub_self]
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [map_sub, map_add, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, f.map_sum z x y h, sub_self]

/-- **The universal property of `ExtSS S J`.** -/
def ExtSS.lift {G : Type*} [AddCommGroup G] (f : ExtSS.Respecting S J G) : ExtSS S J →+ G :=
  QuotientAddGroup.lift (ssRelations S J) (FreeAbelianGroup.lift f.toFun)
    (ExtSS.ssRelations_le_ker f)

theorem ExtSS.lift_mk {G : Type*} [AddCommGroup G] (f : ExtSS.Respecting S J G)
    (x : SSCycle S J) : ExtSS.lift f (ExtSS.mk x) = f.toFun x := by
  show FreeAbelianGroup.lift f.toFun (FreeAbelianGroup.of x) = f.toFun x
  exact FreeAbelianGroup.lift_apply_of f.toFun x

/-- Homomorphisms out of `ExtSS S J` are determined by their values on cycles. -/
theorem ExtSS.hom_ext {G : Type*} [AddCommGroup G] {φ ψ : ExtSS S J →+ G}
    (h : ∀ x : SSCycle S J, φ (ExtSS.mk x) = ψ (ExtSS.mk x)) : φ = ψ :=
  QuotientAddGroup.addMonoidHom_ext _
    (FreeAbelianGroup.lift_ext _ _ fun x => h x)

/-! ### Functoriality -/

/-- The pulled-back semisplit cycle. -/
def SSCycle.comap (f : S →⋆ₙₐ[ℂ] T) (x : SSCycle T J) : SSCycle S J :=
  ⟨x.1.comap f, BusbyCycle.IsSemisplit.comap f x.2⟩

/-- The relation-respecting assignment `x ↦ [x ∘ f]`. -/
def ExtSS.comapRespecting (f : S →⋆ₙₐ[ℂ] T) : ExtSS.Respecting T J (ExtSS S J) where
  toFun x := ExtSS.mk (x.comap f)
  map_split x hx := ExtSS.mk_eq_zero_of_isSplit (x := x.comap f) (BusbyCycle.IsSplit.comap f hx)
  map_unitary x y h :=
    ExtSS.mk_eq_of_isUnitarilyEquivalent (x := x.comap f) (y := y.comap f)
      (BusbyCycle.IsUnitarilyEquivalent.comap f h)
  map_sum z x y h :=
    ExtSS.mk_eq_add_of_isDirectSum (z := z.comap f) (x := x.comap f) (y := y.comap f)
      (BusbyCycle.IsDirectSum.comap f h)

/-- **`Ext⁻¹(-, J)` on morphisms**: the pull-back `f^* : ExtSS T J → ExtSS S J`. -/
def ExtSS.comap (f : S →⋆ₙₐ[ℂ] T) : ExtSS T J →+ ExtSS S J :=
  ExtSS.lift (ExtSS.comapRespecting f)

theorem ExtSS.comap_mk (f : S →⋆ₙₐ[ℂ] T) (x : SSCycle T J) :
    ExtSS.comap f (ExtSS.mk x) = ExtSS.mk (x.comap f) :=
  ExtSS.lift_mk (ExtSS.comapRespecting f) x

theorem SSCycle.comap_id (x : SSCycle S J) : x.comap (NonUnitalStarAlgHom.id ℂ S) = x :=
  Subtype.ext (BusbyCycle.comap_id x.1)

theorem SSCycle.comap_comp (g : T →⋆ₙₐ[ℂ] U) (f : S →⋆ₙₐ[ℂ] T) (x : SSCycle U J) :
    x.comap (g.comp f) = (x.comap g).comap f :=
  Subtype.ext (BusbyCycle.comap_comp g f x.1)

/-- `Ext⁻¹(-, J)` sends the identity to the identity. -/
theorem ExtSS.comap_id :
    (ExtSS.comap (NonUnitalStarAlgHom.id ℂ S) : ExtSS S J →+ ExtSS S J) =
      AddMonoidHom.id (ExtSS S J) := by
  refine ExtSS.hom_ext fun x => ?_
  calc ExtSS.comap (NonUnitalStarAlgHom.id ℂ S) (ExtSS.mk x)
      = ExtSS.mk (x.comap (NonUnitalStarAlgHom.id ℂ S)) := ExtSS.comap_mk _ x
    _ = ExtSS.mk x := congrArg ExtSS.mk (SSCycle.comap_id x)
    _ = AddMonoidHom.id (ExtSS S J) (ExtSS.mk x) := rfl

theorem ExtSS.comap_id_apply (ξ : ExtSS S J) :
    ExtSS.comap (NonUnitalStarAlgHom.id ℂ S) ξ = ξ :=
  DFunLike.congr_fun ExtSS.comap_id ξ

/-- `Ext⁻¹(-, J)` is contravariant: `(g ∘ f)^* = f^* ∘ g^*`. -/
theorem ExtSS.comap_comp (g : T →⋆ₙₐ[ℂ] U) (f : S →⋆ₙₐ[ℂ] T) :
    (ExtSS.comap (g.comp f) : ExtSS U J →+ ExtSS S J) =
      (ExtSS.comap f).comp (ExtSS.comap g) := by
  refine ExtSS.hom_ext fun x => ?_
  calc ExtSS.comap (g.comp f) (ExtSS.mk x)
      = ExtSS.mk (x.comap (g.comp f)) := ExtSS.comap_mk _ x
    _ = ExtSS.mk ((x.comap g).comap f) := congrArg ExtSS.mk (SSCycle.comap_comp g f x)
    _ = ExtSS.comap f (ExtSS.mk (x.comap g)) := (ExtSS.comap_mk f (x.comap g)).symm
    _ = ExtSS.comap f (ExtSS.comap g (ExtSS.mk x)) := by rw [ExtSS.comap_mk g x]

theorem ExtSS.comap_comp_apply (g : T →⋆ₙₐ[ℂ] U) (f : S →⋆ₙₐ[ℂ] T) (ξ : ExtSS U J) :
    ExtSS.comap (g.comp f) ξ = ExtSS.comap f (ExtSS.comap g ξ) :=
  DFunLike.congr_fun (ExtSS.comap_comp g f) ξ

/-! ### Comparison with the Busby-picture group -/

/-- The relation-respecting assignment `x ↦ [x] ∈ ExtGroup S J`. -/
def ExtSS.toExtRespecting : ExtSS.Respecting S J (ExtGroup S J) where
  toFun x := ExtGroup.mk x.1
  map_split _ hx := ExtGroup.mk_eq_zero_of_isSplit hx
  map_unitary _ _ h := ExtGroup.mk_eq_of_isUnitarilyEquivalent h
  map_sum _ _ _ h := ExtGroup.mk_eq_add_of_isDirectSum h

/-- **The forgetful map** `Ext⁻¹(S, J) → Ext(S, J)`. -/
def ExtSS.toExt : ExtSS S J →+ ExtGroup S J :=
  ExtSS.lift ExtSS.toExtRespecting

theorem ExtSS.toExt_mk (x : SSCycle S J) : ExtSS.toExt (ExtSS.mk x) = ExtGroup.mk x.1 :=
  ExtSS.lift_mk ExtSS.toExtRespecting x

/-- The forgetful map is natural. -/
theorem ExtSS.toExt_comap (f : S →⋆ₙₐ[ℂ] T) :
    (ExtSS.toExt.comp (ExtSS.comap f) : ExtSS T J →+ ExtGroup S J) =
      (ExtGroup.comap f).comp ExtSS.toExt := by
  refine ExtSS.hom_ext fun x => ?_
  calc ExtSS.toExt (ExtSS.comap f (ExtSS.mk x))
      = ExtSS.toExt (ExtSS.mk (x.comap f)) := by rw [ExtSS.comap_mk]
    _ = ExtGroup.mk (x.1.comap f) := ExtSS.toExt_mk (x.comap f)
    _ = ExtGroup.comap f (ExtGroup.mk x.1) := (ExtGroup.comap_mk f x.1).symm
    _ = ExtGroup.comap f (ExtSS.toExt (ExtSS.mk x)) := by rw [ExtSS.toExt_mk]

theorem ExtSS.toExt_comap_apply (f : S →⋆ₙₐ[ℂ] T) (ξ : ExtSS T J) :
    ExtSS.toExt (ExtSS.comap f ξ) = ExtGroup.comap f (ExtSS.toExt ξ) :=
  DFunLike.congr_fun (ExtSS.toExt_comap f) ξ

/-- The inverse of the forgetful map when every cycle is semisplit. -/
def ExtSS.ofExtRespecting (h : ∀ x : BusbyCycle S J, x.IsSemisplit) :
    ExtGroup.Respecting S J (ExtSS S J) where
  toFun x := ExtSS.mk ⟨x, h x⟩
  map_split x hx := ExtSS.mk_eq_zero_of_isSplit (x := ⟨x, h x⟩) hx
  map_unitary x y hxy :=
    ExtSS.mk_eq_of_isUnitarilyEquivalent (x := ⟨x, h x⟩) (y := ⟨y, h y⟩) hxy
  map_sum z x y hzxy :=
    ExtSS.mk_eq_add_of_isDirectSum (z := ⟨z, h z⟩) (x := ⟨x, h x⟩) (y := ⟨y, h y⟩) hzxy

/-- **If every Busby cycle of `S` is semisplit, then `Ext⁻¹(S, J) → Ext(S, J)` is bijective.**
By the Choi--Effros lifting theorem the hypothesis holds for nuclear separable `S`. -/
theorem ExtSS.toExt_bijective_of_forall_isSemisplit
    (h : ∀ x : BusbyCycle S J, x.IsSemisplit) :
    Function.Bijective (ExtSS.toExt : ExtSS S J →+ ExtGroup S J) := by
  let g : ExtGroup S J →+ ExtSS S J := ExtGroup.lift (ExtSS.ofExtRespecting h)
  have h₁ : g.comp ExtSS.toExt = AddMonoidHom.id (ExtSS S J) := by
    refine ExtSS.hom_ext fun x => ?_
    calc g (ExtSS.toExt (ExtSS.mk x))
        = g (ExtGroup.mk x.1) := congrArg g (ExtSS.toExt_mk x)
      _ = ExtSS.mk ⟨x.1, h x.1⟩ := ExtGroup.lift_mk (ExtSS.ofExtRespecting h) x.1
      _ = ExtSS.mk x := congrArg ExtSS.mk (Subtype.ext rfl)
      _ = AddMonoidHom.id (ExtSS S J) (ExtSS.mk x) := rfl
  have h₂ : ExtSS.toExt.comp g = AddMonoidHom.id (ExtGroup S J) := by
    refine ExtGroup.hom_ext fun x => ?_
    calc ExtSS.toExt (g (ExtGroup.mk x))
        = ExtSS.toExt (ExtSS.mk ⟨x, h x⟩) :=
          congrArg ExtSS.toExt (ExtGroup.lift_mk (ExtSS.ofExtRespecting h) x)
      _ = ExtGroup.mk x := ExtSS.toExt_mk ⟨x, h x⟩
      _ = AddMonoidHom.id (ExtGroup S J) (ExtGroup.mk x) := rfl
  refine Function.bijective_iff_has_inverse.mpr ⟨g, fun ξ => ?_, fun ξ => ?_⟩
  · exact DFunLike.congr_fun h₁ ξ
  · exact DFunLike.congr_fun h₂ ξ

/-- The forgetful map as an isomorphism, when every Busby cycle of `S` is semisplit. -/
noncomputable def ExtSS.toExtEquiv (h : ∀ x : BusbyCycle S J, x.IsSemisplit) :
    ExtSS S J ≃+ ExtGroup S J :=
  AddEquiv.ofBijective (ExtSS.toExt : ExtSS S J →+ ExtGroup S J)
    (ExtSS.toExt_bijective_of_forall_isSemisplit h)

theorem ExtSS.toExtEquiv_apply (h : ∀ x : BusbyCycle S J, x.IsSemisplit) (ξ : ExtSS S J) :
    ExtSS.toExtEquiv h ξ = ExtSS.toExt ξ :=
  rfl

end Semisplit

end GroupApproximation.Full.TWWSchafhauser
