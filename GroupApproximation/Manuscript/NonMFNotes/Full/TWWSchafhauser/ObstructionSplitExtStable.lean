import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBridge
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseCorners

/-!
# Stable splitting of an Ext cycle gives a stably trivial Busby map

Lane `TWWSch3d4a`, work order `WO-TWWSch-3d4-1` (3), the Busby-ring half.

A vanishing class `[x] = 0` in `Ext(S, J)` means, in stable normal form, that
`x ⊕ s ≃ w` for split cycles `s`, `w` (Blackadar, *K-theory for operator algebras*, §15.6;
Kasparov, J. Soviet Math. 1980, §7). This file shows that this normal form makes the Busby map
of `x` stably trivial in the sense of `IsStablyTrivialBusby` (`ObstructionSplit.lean`), in the
corona `StdCorona J` with the Cuntz pair `stdCuntzPair J` and the class of all trivial
extensions `Set.univ`:

* `BusbyCycle.IsUnitallySplit`: split by a unital representation;
  `IsUnitallySplit.isSplit`, `IsUnitallySplit.isUnital`, `IsUnitallySplit.isTrivialBusby`;
* `BusbyCycle.IsUnitarilyEquivalent.isUnital_of_isUnital`: unitality transfers back along a
  unitary equivalence;
* `BusbyCycle.busby_eq_comp_stdRepHom`: the Busby map of a unitally split cycle is `π ∘ σ`;
* `BusbyCycle.isStablyTrivialBusby_of_isDirectSum`: if `z = x ⊕ s` and `z ≃ w` with `s`, `w`
  unitally split, then `x.busby` is stably trivial.

The Ext-side statement (`ExtGroup.mk x = 0` gives such `s`, `z`, `w`) is 3d-2's
`ExtGroup.mk_eq_zero_iff` / `exists_split_of_mk_eq_zero` (`ObstructionExtZero.lean`).
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Stable

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A cycle is **unitally split** when its lift is, modulo compacts, a unital representation. -/
def BusbyCycle.IsUnitallySplit (x : BusbyCycle S J) : Prop :=
  ∃ ρ : S → StdOp J, IsRepresentation (standardModule ℕ J) ρ ∧ (∀ v, (ρ 1).toFun v = v) ∧
    ∀ a : S, CompactEq J (x.lift a) (ρ a)

theorem BusbyCycle.IsUnitallySplit.isSplit {x : BusbyCycle S J} (h : x.IsUnitallySplit) :
    x.IsSplit := by
  obtain ⟨ρ, hρ, _, hc⟩ := h
  exact ⟨ρ, hρ, hc⟩

theorem BusbyCycle.IsUnitallySplit.isUnital {x : BusbyCycle S J} (h : x.IsUnitallySplit) :
    x.IsUnital := by
  obtain ⟨ρ, _, h1, hc⟩ := h
  have h1' : CompactEq J (ρ 1) (Adjointable.id (standardModule ℕ J)) :=
    compactEq_of_toFun_eq h1
  show CompactEq J (x.lift 1) (Adjointable.id (standardModule ℕ J))
  exact compactEq_trans (hc 1) h1'

/-- A unitally split cycle has a trivial Busby map. -/
theorem BusbyCycle.IsUnitallySplit.isTrivialBusby {x : BusbyCycle S J} (hx : x.IsUnital)
    (h : x.IsUnitallySplit) : IsTrivialBusby (stdCoronaQuot J) (x.busby hx) := by
  obtain ⟨ρ, hρ, h1, hc⟩ := h
  exact x.isTrivialBusby_of_isSplit hx hρ h1 hc

/-- **Unitality transfers back along a unitary equivalence**: if `U x(1) U⋆ ≡ y(1)` and
`y(1) ≡ 1`, then `x(1) = U⋆ (U x(1) U⋆) U ≡ U⋆ U = 1`. -/
theorem BusbyCycle.IsUnitarilyEquivalent.isUnital_of_isUnital {x y : BusbyCycle S J}
    (h : x.IsUnitarilyEquivalent y) (hy : y.IsUnital) : x.IsUnital := by
  obtain ⟨U, hU, hc⟩ := h
  have h1 : CompactEq J (Adjointable.comp U (Adjointable.comp (x.lift 1) (Adjointable.adjoint U)))
      (Adjointable.id (standardModule ℕ J)) :=
    compactEq_trans (hc 1) hy
  have h2 : CompactEq J
      (Adjointable.comp (Adjointable.adjoint U)
        (Adjointable.comp
          (Adjointable.comp U (Adjointable.comp (x.lift 1) (Adjointable.adjoint U))) U))
      (Adjointable.comp (Adjointable.adjoint U)
        (Adjointable.comp (Adjointable.id (standardModule ℕ J)) U)) :=
    (h1.comp_right hU.isBounded).comp_left hU.adjoint.isBounded
  have h3 : CompactEq J (x.lift 1)
      (Adjointable.comp (Adjointable.adjoint U)
        (Adjointable.comp
          (Adjointable.comp U (Adjointable.comp (x.lift 1) (Adjointable.adjoint U))) U)) :=
    compactEq_of_toFun_eq fun v =>
      ((congrArg (fun w => U.adj (U.toFun ((x.lift 1).toFun w))) (hU.adj_toFun v)).trans
        (hU.adj_toFun ((x.lift 1).toFun v))).symm
  have h4 : CompactEq J
      (Adjointable.comp (Adjointable.adjoint U)
        (Adjointable.comp (Adjointable.id (standardModule ℕ J)) U))
      (Adjointable.id (standardModule ℕ J)) :=
    compactEq_of_toFun_eq fun v => hU.adj_toFun v
  show CompactEq J (x.lift 1) (Adjointable.id (standardModule ℕ J))
  exact compactEq_trans h3 (compactEq_trans h2 h4)

/-- The Busby map of a cycle split by a unital representation `ρ` is `π ∘ σ_ρ`. -/
theorem BusbyCycle.busby_eq_comp_stdRepHom {x : BusbyCycle S J} (hx : x.IsUnital)
    {ρ : S → StdOp J} (hρ : IsRepresentation (standardModule ℕ J) ρ)
    (h1 : ∀ v, (ρ 1).toFun v = v) (hc : ∀ a : S, CompactEq J (x.lift a) (ρ a)) :
    (stdCoronaQuot J).comp (stdRepHom ρ hρ h1) = x.busby hx :=
  StarAlgHom.ext fun a =>
    (stdCoronaQuot_eq_iff (stdRepHom ρ hρ h1 a) (x.bddLift a)).mpr (compactEq_symm (hc a))

/-- **Stable splitting gives a stably trivial Busby map** (WO-TWWSch-3d4-1 (3), Busby half):
if `z` is a direct sum of `x` and a unitally split `s`, and `z` is unitarily equivalent to a
unitally split `w`, then `x.busby ⊕ π ∘ σ_s ≃ π ∘ σ_w` in `StdCorona J`, with the Cuntz sum of
`stdCuntzPair J`. -/
theorem BusbyCycle.isStablyTrivialBusby_of_isDirectSum {x s z w : BusbyCycle S J}
    (hx : x.IsUnital) (hs : s.IsUnitallySplit) (hw : w.IsUnitallySplit)
    (hsum : z.IsDirectSum x s) (hzw : z.IsUnitarilyEquivalent w) :
    IsStablyTrivialBusby (stdCoronaQuot J) (stdCuntzPair J)
      (Set.univ : Set (S →⋆ₐ[ℂ] StdBdd J)) (x.busby hx) := by
  have hs1 : s.IsUnital := hs.isUnital
  have hw1 : w.IsUnital := hw.isUnital
  have hz1 : z.IsUnital := hzw.isUnital_of_isUnital hw1
  obtain ⟨ρ, hρ, hρ1, hsρ⟩ := hs
  obtain ⟨ρ', hρ', hρ'1, hwρ'⟩ := hw
  have key : IsUnitarilyEquivalentBusby ((stdCuntzPair J).sumBusby (x.busby hx) (s.busby hs1))
      (w.busby hw1) :=
    (hsum.isUnitarilyEquivalentBusby hz1 hx hs1).trans (hzw.isUnitarilyEquivalentBusby hz1 hw1)
  rw [← s.busby_eq_comp_stdRepHom hs1 hρ hρ1 hsρ,
    ← w.busby_eq_comp_stdRepHom hw1 hρ' hρ'1 hwρ'] at key
  exact ⟨stdRepHom ρ hρ hρ1, Set.mem_univ _, stdRepHom ρ' hρ' hρ'1, key⟩

end Stable

end GroupApproximation.Full.TWWSchafhauser

end
