import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtMapOps
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBusby
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetComap

/-!
# `Ext(S, -)` as a covariant functor of the coefficient algebra

Lane `TWWSch3d2Nat`, work order `WO-TWWSch-3d2-Nat`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1370). There the obstruction class in `KK¹(S, J) = Ext(S, J)`
is moved along maps of `J`. The push-forward of an extension along `f : J → J'` has the Busby
map `f_* ∘ τ` (G. G. Kasparov, Izv. Akad. Nauk SSSR 44 (1980), §7; B. Blackadar, *K-theory for
operator algebras*, 13.5 and 17.1).

The operator-level datum is a `CoronaPushforward J J'` (`ObstructionExtMapOps`). This file proves
that every push-forward acts on `Ext`, functorially:

* `BusbyCycle.mapOf Φ x`: the lift is `a ↦ Φ(x(a))`;
* `BusbyCycle.IsSplit.mapOf`, `BusbyCycle.IsUnitarilyEquivalent.mapOf`,
  `BusbyCycle.IsDirectSum.mapOf`: the three defining relations of `Ext` are preserved. A unitary
  `U` goes to the unitary `Φ(U) + (1 - Φ(1))`. A direct sum under any unitary goes to a direct
  sum, by `CoronaPushforward.exists_unitary_sum`;
* `BusbyCycle.mapOf_id`, `BusbyCycle.mapOf_comp`: functoriality on the nose at the cycle level;
* `ExtGroup.mapOf Φ : ExtGroup S J →+ ExtGroup S J'`, `mapOf_mk`, `mapOf_id`, `mapOf_comp`;
* `ExtGroup.mapOf_eq_of_isEquivalent`: push-forwards that agree up to one unitary and compacts
  induce the same homomorphism.

## Status of `ExtGroup.map f` for a `⋆`-homomorphism `f : J →⋆ₙₐ[ℂ] J'`

The work order asks for `BusbyCycle.map f` and `ExtGroup.map f`. Here they would be
`x.mapOf (CoronaPushforward.ofHom f)` and `ExtGroup.mapOf (CoronaPushforward.ofHom f)`. Building
`ofHom f` needs the interior tensor product `H_J ⊗_f J'` and Kasparov stabilization, and neither
is in the repository. That construction was sent to `main` as a work order. It asks for:

* `CoronaPushforward.ofHom f`, i.e. `T ↦ V (T ⊗ 1) V⋆`;
* `ofHom_id : (ofHom id).IsEquivalent (CoronaPushforward.id J)`;
* `ofHom_comp : (ofHom (g.comp f)).IsEquivalent ((ofHom g).comp (ofHom f))`.

With these, `map_id` and `map_comp` follow at once from `mapOf_eq_of_isEquivalent`, `mapOf_id`
and `mapOf_comp`. That is the "up to unitary equivalence at the cycle level" statement asked for.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

variable {S : Type} [NonUnitalCStarAlgebra S]
variable {J J' J'' : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [NonUnitalCStarAlgebra J'] [PartialOrder J'] [StarOrderedRing J']
  [NonUnitalCStarAlgebra J''] [PartialOrder J''] [StarOrderedRing J'']

/-! ## Push-forward of a Busby cycle -/

/-- **The pushed-forward Busby cycle** along a corona push-forward `Φ`. Its lift is
`a ↦ Φ(x(a))`, and the four homomorphism clauses modulo compacts are carried over by
`CoronaPushforward.compactEq`. -/
def BusbyCycle.mapOf (Φ : CoronaPushforward J J') (x : BusbyCycle S J) : BusbyCycle S J' where
  lift a := (Φ.toHom (x.bddLift a) : StdOp J')
  bounded a := ExtMap.coe_isBounded (Φ.toHom (x.bddLift a))
  map_add a a' := by
    have h := Φ.compactEq (A := x.bddLift (a + a')) (B := x.bddLift a + x.bddLift a')
      (x.map_add a a')
    rw [_root_.map_add Φ.toHom] at h
    exact h
  map_smul c a := by
    have h := Φ.compactEq (A := x.bddLift (c • a)) (B := c • x.bddLift a) (x.map_smul c a)
    rw [_root_.map_smul Φ.toHom] at h
    exact h
  map_mul a a' := by
    have h := Φ.compactEq (A := x.bddLift (a * a')) (B := x.bddLift a * x.bddLift a')
      (x.map_mul a a')
    rw [_root_.map_mul Φ.toHom] at h
    exact h
  map_star a := by
    have h := Φ.compactEq (A := x.bddLift (star a)) (B := star (x.bddLift a)) (x.map_star a)
    rw [_root_.map_star Φ.toHom] at h
    exact h

theorem BusbyCycle.mapOf_lift (Φ : CoronaPushforward J J') (x : BusbyCycle S J) (a : S) :
    (x.mapOf Φ).lift a = (Φ.toHom (x.bddLift a) : StdOp J') :=
  rfl

/-- A representation, as a map into the bounded operators. -/
def ExtMap.repBdd {ρ : S → StdOp J} (hρ : IsRepresentation (standardModule ℕ J) ρ) (a : S) :
    StdBdd J :=
  ExtMap.toBdd (ρ a) (hρ.bounded a)

/-- A push-forward of a representation is a representation. -/
theorem ExtMap.isRepresentation_pushforward (Φ : CoronaPushforward J J') {ρ : S → StdOp J}
    (hρ : IsRepresentation (standardModule ℕ J) ρ) :
    IsRepresentation (standardModule ℕ J')
      (fun a : S => (Φ.toHom (ExtMap.repBdd hρ a) : StdOp J')) where
  bounded a := ExtMap.coe_isBounded (Φ.toHom (ExtMap.repBdd hρ a))
  map_add a a' v :=
    congrArg (fun T : StdBdd J' => (T : StdOp J').toFun v)
      ((congrArg Φ.toHom (ExtMap.bdd_ext (T := ExtMap.repBdd hρ (a + a'))
        (U := ExtMap.repBdd hρ a + ExtMap.repBdd hρ a') (hρ.map_add a a'))).trans
        (_root_.map_add Φ.toHom _ _))
  map_smul c a v :=
    congrArg (fun T : StdBdd J' => (T : StdOp J').toFun v)
      ((congrArg Φ.toHom (ExtMap.bdd_ext (T := ExtMap.repBdd hρ (c • a))
        (U := c • ExtMap.repBdd hρ a) (hρ.map_smul c a))).trans
        (_root_.map_smul Φ.toHom _ _))
  map_mul a a' v :=
    congrArg (fun T : StdBdd J' => (T : StdOp J').toFun v)
      ((congrArg Φ.toHom (ExtMap.bdd_ext (T := ExtMap.repBdd hρ (a * a'))
        (U := ExtMap.repBdd hρ a * ExtMap.repBdd hρ a') (hρ.map_mul a a'))).trans
        (_root_.map_mul Φ.toHom _ _))
  map_star a v :=
    congrArg (fun T : StdBdd J' => (T : StdOp J').toFun v)
      ((congrArg Φ.toHom (ExtMap.bdd_ext (T := ExtMap.repBdd hρ (star a))
        (U := star (ExtMap.repBdd hρ a)) (hρ.map_star a))).trans
        (_root_.map_star Φ.toHom _))

/-- Pushing forward a split cycle gives a split cycle. The splitting representation is pushed
forward too. -/
theorem BusbyCycle.IsSplit.mapOf (Φ : CoronaPushforward J J') {x : BusbyCycle S J}
    (hx : x.IsSplit) : (x.mapOf Φ).IsSplit := by
  obtain ⟨ρ, hρ, hxρ⟩ := hx
  exact ⟨fun a => (Φ.toHom (ExtMap.repBdd hρ a) : StdOp J'),
    ExtMap.isRepresentation_pushforward Φ hρ,
    fun a => Φ.compactEq (A := x.bddLift a) (B := ExtMap.repBdd hρ a) (hxρ a)⟩

/-- Pushing forward preserves unitary equivalence. The unitary `U` goes to the unitary
`Φ(U) + (1 - Φ(1))`. -/
theorem BusbyCycle.IsUnitarilyEquivalent.mapOf (Φ : CoronaPushforward J J')
    {x y : BusbyCycle S J} (h : x.IsUnitarilyEquivalent y) :
    (x.mapOf Φ).IsUnitarilyEquivalent (y.mapOf Φ) := by
  obtain ⟨U, hU, hxy⟩ := h
  have hu := Φ.unitize_unitary (ExtMap.star_mul_toBdd hU) (ExtMap.mul_star_toBdd hU)
  refine ⟨(Φ.unitize (ExtMap.toBdd U hU.isBounded) : StdOp J'),
    ExtMap.isUnitaryAdj_of_bdd hu.1 hu.2, fun a => ?_⟩
  have h2 := Φ.compactEq
    (A := ExtMap.toBdd U hU.isBounded * (x.bddLift a * star (ExtMap.toBdd U hU.isBounded)))
    (B := y.bddLift a) (hxy a)
  rw [← Φ.unitize_conj, ExtMap.coe_mul_mul_star] at h2
  exact h2

/-- Pushing forward preserves direct sums (`CoronaPushforward.exists_unitary_sum`). -/
theorem BusbyCycle.IsDirectSum.mapOf (Φ : CoronaPushforward J J') {z x y : BusbyCycle S J}
    (h : z.IsDirectSum x y) : (z.mapOf Φ).IsDirectSum (x.mapOf Φ) (y.mapOf Φ) := by
  obtain ⟨U, hU, hzxy⟩ := h
  obtain ⟨U', hU', hsum⟩ := Φ.exists_unitary_sum hU
  exact ⟨U', hU', fun a => hsum (x.bddLift a) (y.bddLift a) (z.bddLift a) (hzxy a)⟩

/-- The identity push-forward fixes every cycle. -/
theorem BusbyCycle.mapOf_id (x : BusbyCycle S J) : x.mapOf (CoronaPushforward.id J) = x :=
  BusbyCycle.ext_lift rfl

/-- Pushing forward along a composite is the composite of the push-forwards. -/
theorem BusbyCycle.mapOf_comp (Ψ : CoronaPushforward J' J'') (Φ : CoronaPushforward J J')
    (x : BusbyCycle S J) : x.mapOf (Ψ.comp Φ) = (x.mapOf Φ).mapOf Ψ :=
  BusbyCycle.ext_lift rfl

/-! ## The induced homomorphism of `Ext` -/

/-- The relation-respecting assignment `x ↦ [Φ ∘ x]`. -/
def ExtGroup.mapOfRespecting (Φ : CoronaPushforward J J') :
    ExtGroup.Respecting S J (ExtGroup S J') where
  toFun x := ExtGroup.mk (x.mapOf Φ)
  map_split x hx := ExtGroup.mk_eq_zero_of_isSplit (hx.mapOf Φ)
  map_unitary x y h := ExtGroup.mk_eq_of_isUnitarilyEquivalent (h.mapOf Φ)
  map_sum z x y h := ExtGroup.mk_eq_add_of_isDirectSum (h.mapOf Φ)

/-- **`Ext(S, -)` on push-forwards**: `Φ_* : Ext(S, J) → Ext(S, J')`. -/
def ExtGroup.mapOf (Φ : CoronaPushforward J J') : ExtGroup S J →+ ExtGroup S J' :=
  ExtGroup.lift (ExtGroup.mapOfRespecting Φ)

theorem ExtGroup.mapOf_mk (Φ : CoronaPushforward J J') (x : BusbyCycle S J) :
    ExtGroup.mapOf Φ (ExtGroup.mk x) = ExtGroup.mk (x.mapOf Φ) :=
  ExtGroup.lift_mk (ExtGroup.mapOfRespecting Φ) x

/-- `Ext(S, -)` sends the identity push-forward to the identity. -/
theorem ExtGroup.mapOf_id :
    (ExtGroup.mapOf (CoronaPushforward.id J) : ExtGroup S J →+ ExtGroup S J) =
      AddMonoidHom.id (ExtGroup S J) := by
  refine ExtGroup.hom_ext fun x => ?_
  calc ExtGroup.mapOf (CoronaPushforward.id J) (ExtGroup.mk x)
      = ExtGroup.mk (x.mapOf (CoronaPushforward.id J)) := ExtGroup.mapOf_mk _ x
    _ = ExtGroup.mk x := congrArg ExtGroup.mk (BusbyCycle.mapOf_id x)
    _ = AddMonoidHom.id (ExtGroup S J) (ExtGroup.mk x) := rfl

/-- `Ext(S, -)` is covariant: `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`. -/
theorem ExtGroup.mapOf_comp (Ψ : CoronaPushforward J' J'') (Φ : CoronaPushforward J J') :
    (ExtGroup.mapOf (Ψ.comp Φ) : ExtGroup S J →+ ExtGroup S J'') =
      (ExtGroup.mapOf Ψ).comp (ExtGroup.mapOf Φ) := by
  refine ExtGroup.hom_ext fun x => ?_
  calc ExtGroup.mapOf (Ψ.comp Φ) (ExtGroup.mk x)
      = ExtGroup.mk (x.mapOf (Ψ.comp Φ)) := ExtGroup.mapOf_mk _ x
    _ = ExtGroup.mk ((x.mapOf Φ).mapOf Ψ) := congrArg ExtGroup.mk (BusbyCycle.mapOf_comp Ψ Φ x)
    _ = ExtGroup.mapOf Ψ (ExtGroup.mk (x.mapOf Φ)) := (ExtGroup.mapOf_mk Ψ (x.mapOf Φ)).symm
    _ = ExtGroup.mapOf Ψ (ExtGroup.mapOf Φ (ExtGroup.mk x)) := by rw [ExtGroup.mapOf_mk Φ x]

theorem ExtGroup.mapOf_comp_apply (Ψ : CoronaPushforward J' J'') (Φ : CoronaPushforward J J')
    (ξ : ExtGroup S J) :
    ExtGroup.mapOf (Ψ.comp Φ) ξ = ExtGroup.mapOf Ψ (ExtGroup.mapOf Φ ξ) :=
  DFunLike.congr_fun (ExtGroup.mapOf_comp Ψ Φ) ξ

/-- **Equivalent push-forwards induce the same map on `Ext`.** If `Φ` and `Φ'` agree up to one
unitary of `H_{J'}` and compacts, then every pushed-forward cycle `Φ ∘ x` is unitarily equivalent
to `Φ' ∘ x`. This is how `ofHom id = id` and `ofHom (g ∘ f) = ofHom g ∘ ofHom f` reach `Ext`
(Blackadar 17.1). -/
theorem ExtGroup.mapOf_eq_of_isEquivalent {Φ Φ' : CoronaPushforward J J'}
    (h : Φ.IsEquivalent Φ') :
    (ExtGroup.mapOf Φ : ExtGroup S J →+ ExtGroup S J') = ExtGroup.mapOf Φ' := by
  obtain ⟨R, hR, hRT⟩ := h
  refine ExtGroup.hom_ext fun x => ?_
  rw [ExtGroup.mapOf_mk, ExtGroup.mapOf_mk]
  exact ExtGroup.mk_eq_of_isUnitarilyEquivalent (x := x.mapOf Φ) (y := x.mapOf Φ')
    ⟨R, hR, fun a => hRT (x.bddLift a)⟩

theorem ExtGroup.mapOf_apply_eq_of_isEquivalent {Φ Φ' : CoronaPushforward J J'}
    (h : Φ.IsEquivalent Φ') (ξ : ExtGroup S J) : ExtGroup.mapOf Φ ξ = ExtGroup.mapOf Φ' ξ :=
  DFunLike.congr_fun (ExtGroup.mapOf_eq_of_isEquivalent h) ξ

end GroupApproximation.Full.TWWSchafhauser

end
