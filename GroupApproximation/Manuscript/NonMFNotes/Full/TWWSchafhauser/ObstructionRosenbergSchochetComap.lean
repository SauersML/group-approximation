import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExt

/-!
# `Ext(-, J)` as a contravariant functor of the first variable

Lane `TWWSch3d3c`, work order `WO-TWWSchafhauser-3d3-3` (Rosenberg–Schochet injectivity half).
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter through C. Schafhauser, J. reine angew. Math. 759 (2020),
§§4--5. There the UCT kills the obstruction class in `KK¹(S, J)`.

To transfer a statement about `Ext(C, J)` along a `KK`-equivalence `S ∼ C`, we need `Ext(-, J)`
to be a functor of the first variable. The Busby map of the pulled-back extension along
`φ : A → B` is the composite `τ ∘ φ` (J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §1;
B. Blackadar, *K-theory for operator algebras*, 15.6). In the Busby-cycle picture of
`ObstructionExt`, this is composition of the lift with `φ`.

* `BusbyCycle.comap φ x`: the lift is `x.lift ∘ φ`;
* `BusbyCycle.IsSplit.comap`, `BusbyCycle.IsUnitarilyEquivalent.comap`,
  `BusbyCycle.IsDirectSum.comap`: the three defining relations are preserved;
* `ExtGroup.comap φ : ExtGroup B J →+ ExtGroup A J`, `comap_mk`, `comap_id`, `comap_comp`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Comap

variable {A B C : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Two Busby cycles with the same lift are equal. The remaining fields are proofs. -/
theorem BusbyCycle.ext_lift {x y : BusbyCycle A J} (h : x.lift = y.lift) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- **The pulled-back Busby cycle** along `φ : A → B`. Its lift is `x.lift ∘ φ`. -/
def BusbyCycle.comap (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) : BusbyCycle A J where
  lift a := x.lift (φ a)
  bounded a := x.bounded (φ a)
  map_add a a' := by
    show CompactEq J (x.lift (φ (a + a'))) (Adjointable.add (x.lift (φ a)) (x.lift (φ a')))
    rw [_root_.map_add]
    exact x.map_add (φ a) (φ a')
  map_smul c a := by
    show CompactEq J (x.lift (φ (c • a))) (Adjointable.smul c (x.lift (φ a)))
    rw [_root_.map_smul]
    exact x.map_smul c (φ a)
  map_mul a a' := by
    show CompactEq J (x.lift (φ (a * a'))) (Adjointable.comp (x.lift (φ a)) (x.lift (φ a')))
    rw [_root_.map_mul]
    exact x.map_mul (φ a) (φ a')
  map_star a := by
    show CompactEq J (x.lift (φ (star a))) (Adjointable.adjoint (x.lift (φ a)))
    rw [_root_.map_star]
    exact x.map_star (φ a)

theorem BusbyCycle.comap_lift (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) (a : A) :
    (x.comap φ).lift a = x.lift (φ a) :=
  rfl

/-- A representation composed with a `⋆`-homomorphism is a representation. -/
theorem isRepresentation_comp (φ : A →⋆ₙₐ[ℂ] B) {ρ : B → StdOp J}
    (hρ : IsRepresentation (standardModule ℕ J) ρ) :
    IsRepresentation (standardModule ℕ J) (fun a : A => ρ (φ a)) where
  bounded a := hρ.bounded (φ a)
  map_add a a' v := by
    show (ρ (φ (a + a'))).toFun v = (ρ (φ a)).toFun v + (ρ (φ a')).toFun v
    rw [_root_.map_add]
    exact hρ.map_add (φ a) (φ a') v
  map_smul c a v := by
    show (ρ (φ (c • a))).toFun v = c • (ρ (φ a)).toFun v
    rw [_root_.map_smul]
    exact hρ.map_smul c (φ a) v
  map_mul a a' v := by
    show (ρ (φ (a * a'))).toFun v = (ρ (φ a)).toFun ((ρ (φ a')).toFun v)
    rw [_root_.map_mul]
    exact hρ.map_mul (φ a) (φ a') v
  map_star a v := by
    show (ρ (φ (star a))).toFun v = (ρ (φ a)).adj v
    rw [_root_.map_star]
    exact hρ.map_star (φ a) v

/-- Pulling back a split cycle gives a split cycle. -/
theorem BusbyCycle.IsSplit.comap (φ : A →⋆ₙₐ[ℂ] B) {x : BusbyCycle B J} (hx : x.IsSplit) :
    (x.comap φ).IsSplit := by
  obtain ⟨ρ, hρ, hxρ⟩ := hx
  exact ⟨fun a => ρ (φ a), isRepresentation_comp φ hρ, fun a => hxρ (φ a)⟩

/-- Pulling back preserves unitary equivalence, with the same unitary. -/
theorem BusbyCycle.IsUnitarilyEquivalent.comap (φ : A →⋆ₙₐ[ℂ] B) {x y : BusbyCycle B J}
    (h : x.IsUnitarilyEquivalent y) : (x.comap φ).IsUnitarilyEquivalent (y.comap φ) := by
  obtain ⟨U, hU, hxy⟩ := h
  exact ⟨U, hU, fun a => hxy (φ a)⟩

/-- Pulling back preserves direct sums, with the same unitary. -/
theorem BusbyCycle.IsDirectSum.comap (φ : A →⋆ₙₐ[ℂ] B) {z x y : BusbyCycle B J}
    (h : z.IsDirectSum x y) : (z.comap φ).IsDirectSum (x.comap φ) (y.comap φ) := by
  obtain ⟨U, hU, hzxy⟩ := h
  exact ⟨U, hU, fun a => hzxy (φ a)⟩

theorem BusbyCycle.comap_id (x : BusbyCycle A J) :
    x.comap (NonUnitalStarAlgHom.id ℂ A) = x :=
  BusbyCycle.ext_lift rfl

theorem BusbyCycle.comap_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle C J) :
    x.comap (ψ.comp φ) = (x.comap ψ).comap φ :=
  BusbyCycle.ext_lift rfl

/-- The relation-respecting assignment `x ↦ [x ∘ φ]`. -/
def ExtGroup.comapRespecting (φ : A →⋆ₙₐ[ℂ] B) : ExtGroup.Respecting B J (ExtGroup A J) where
  toFun x := ExtGroup.mk (x.comap φ)
  map_split x hx := ExtGroup.mk_eq_zero_of_isSplit (hx.comap φ)
  map_unitary x y h := ExtGroup.mk_eq_of_isUnitarilyEquivalent (h.comap φ)
  map_sum z x y h := ExtGroup.mk_eq_add_of_isDirectSum (h.comap φ)

/-- **`Ext(-, J)` on morphisms**: the pull-back `φ^* : Ext(B, J) → Ext(A, J)`. -/
def ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) : ExtGroup B J →+ ExtGroup A J :=
  ExtGroup.lift (ExtGroup.comapRespecting φ)

theorem ExtGroup.comap_mk (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) :
    ExtGroup.comap φ (ExtGroup.mk x) = ExtGroup.mk (x.comap φ) :=
  ExtGroup.lift_mk (ExtGroup.comapRespecting φ) x

/-- `Ext(-, J)` sends the identity to the identity. -/
theorem ExtGroup.comap_id :
    (ExtGroup.comap (NonUnitalStarAlgHom.id ℂ A) : ExtGroup A J →+ ExtGroup A J) =
      AddMonoidHom.id (ExtGroup A J) := by
  refine ExtGroup.hom_ext fun x => ?_
  calc ExtGroup.comap (NonUnitalStarAlgHom.id ℂ A) (ExtGroup.mk x)
      = ExtGroup.mk (x.comap (NonUnitalStarAlgHom.id ℂ A)) := ExtGroup.comap_mk _ x
    _ = ExtGroup.mk x := congrArg ExtGroup.mk (BusbyCycle.comap_id x)
    _ = AddMonoidHom.id (ExtGroup A J) (ExtGroup.mk x) := rfl

/-- `Ext(-, J)` is contravariant: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem ExtGroup.comap_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    (ExtGroup.comap (ψ.comp φ) : ExtGroup C J →+ ExtGroup A J) =
      (ExtGroup.comap φ).comp (ExtGroup.comap ψ) := by
  refine ExtGroup.hom_ext fun x => ?_
  calc ExtGroup.comap (ψ.comp φ) (ExtGroup.mk x)
      = ExtGroup.mk (x.comap (ψ.comp φ)) := ExtGroup.comap_mk _ x
    _ = ExtGroup.mk ((x.comap ψ).comap φ) := congrArg ExtGroup.mk (BusbyCycle.comap_comp ψ φ x)
    _ = ExtGroup.comap φ (ExtGroup.mk (x.comap ψ)) := (ExtGroup.comap_mk φ (x.comap ψ)).symm
    _ = ExtGroup.comap φ (ExtGroup.comap ψ (ExtGroup.mk x)) := by rw [ExtGroup.comap_mk ψ x]

theorem ExtGroup.comap_comp_apply (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) (ξ : ExtGroup C J) :
    ExtGroup.comap (ψ.comp φ) ξ = ExtGroup.comap φ (ExtGroup.comap ψ ξ) :=
  DFunLike.congr_fun (ExtGroup.comap_comp ψ φ) ξ

end Comap

end GroupApproximation.Full.TWWSchafhauser
