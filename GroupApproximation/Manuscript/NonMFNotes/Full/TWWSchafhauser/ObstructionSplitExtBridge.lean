import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBusby
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplit

/-!
# From Ext-cycle relations to Busby-ring relations

Lane `TWWSch3d4a`, work order `WO-TWWSch-3d4-1`, fourth part.

The relations that define `ExtGroup S J` (`ObstructionExt.lean`) are stated on lifts in `𝓛(H_J)`:
split cycles, unitary equivalence, direct sums under a unitary `H_J ⊕ H_J ≅ H_J`. The absorption
framework (`ObstructionSplit*.lean`) states them on Busby maps into a ring `Q`. This file
translates each relation for unital cycles, with `Q = StdCorona J`, `π = stdCoronaQuot J`, and
the Cuntz pair `stdCuntzPair J` (Blackadar, *K-theory for operator algebras*, §15.6;
Elliott–Kucerovsky, Pacific J. Math. 198 (2001), §1):

* `stdBddOfUnitary`, `stdBddOfUnitary_mem`: a unitary on `H_J` is a unitary of `StdBdd J`;
* `BusbyCycle.IsUnitarilyEquivalent.isUnitarilyEquivalentBusby`;
* `BusbyCycle.IsDirectSum.isUnitarilyEquivalentBusby`: a direct sum `z` of `x` and `y` is
  unitarily equivalent to the Cuntz sum `(stdCuntzPair J).sumBusby (x.busby) (y.busby)`;
* `stdRepHom`: a unital representation `S → 𝓛(H_J)` as a `⋆`-homomorphism `S → StdBdd J`, and
  `isRepresentation_starAlgHom` for the converse;
* `BusbyCycle.isTrivialBusby_of_isSplit`: a cycle split by a unital representation has a
  trivial Busby map.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Unitary

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A unitary operator on `H_J` as an element of `StdBdd J`. -/
def stdBddOfUnitary {U : StdOp J} (hU : U.IsUnitaryAdj) : StdBdd J :=
  ⟨U, mem_boundedAdj.mpr hU.isBounded⟩

theorem stdBddOfUnitary_mem {U : StdOp J} (hU : U.IsUnitaryAdj) :
    stdBddOfUnitary hU ∈ unitary (StdBdd J) :=
  Unitary.mem_iff.mpr ⟨Subtype.ext (adjointable_ext fun v => hU.adj_toFun v),
    Subtype.ext (adjointable_ext fun v => hU.toFun_adj v)⟩

/-- `V⋆(V(a, 0) + V(0, b)) = (a, b)` for the unitary merge `V : H_J ⊕ H_J → H_J`. -/
theorem natSumMerge_adj_add (a b : (standardModule ℕ J).carrier) :
    (Adjointable.natSumMerge J).adj ((Adjointable.natSumMerge J).toFun (a, 0)
      + (Adjointable.natSumMerge J).toFun (0, b)) = (a, b) := by
  have hp : ((a, 0) : (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J)).carrier)
      + ((0, b) : (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J)).carrier)
      = ((a, b) : (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J)).carrier) :=
    Prod.ext (add_zero a) (zero_add b)
  exact (congrArg (Adjointable.natSumMerge J).adj
      (Adjointable.map_add (Adjointable.natSumMerge J) (a, 0) (0, b)).symm).trans
    (((Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun _).trans hp)

end Unitary

section Relations

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Unitarily equivalent cycles have unitarily equivalent Busby maps.** -/
theorem BusbyCycle.IsUnitarilyEquivalent.isUnitarilyEquivalentBusby {x y : BusbyCycle S J}
    (h : x.IsUnitarilyEquivalent y) (hx : x.IsUnital) (hy : y.IsUnital) :
    IsUnitarilyEquivalentBusby (x.busby hx) (y.busby hy) := by
  obtain ⟨U, hU, hc⟩ := h
  refine ⟨stdCoronaQuot J (stdBddOfUnitary hU),
    Unitary.map_mem (stdCoronaQuot J) (stdBddOfUnitary_mem hU), fun a => ?_⟩
  have hA : (stdBddOfUnitary hU * x.bddLift a * star (stdBddOfUnitary hU)).1
      = Adjointable.comp U (Adjointable.comp (x.lift a) (Adjointable.adjoint U)) :=
    adjointable_ext fun _ => rfl
  have hq : stdCoronaQuot J (y.bddLift a)
      = stdCoronaQuot J (stdBddOfUnitary hU * x.bddLift a * star (stdBddOfUnitary hU)) := by
    refine (stdCoronaQuot_eq_iff _ _).mpr ?_
    rw [hA]
    exact compactEq_symm (hc a)
  rw [map_mul, map_mul, map_star] at hq
  exact hq

/-- **A direct sum is the Cuntz sum of the Busby maps**, up to unitary equivalence in the
corona: if `z ≡ U(x ⊕ y)U⋆` then `z ≃ s₁ x s₁⋆ + s₂ y s₂⋆` through `W = U V⋆`, with
`V = natSumMerge J` the unitary that defines the even/odd isometries `s₁ = V ι₁`, `s₂ = V ι₂`. -/
theorem BusbyCycle.IsDirectSum.isUnitarilyEquivalentBusby {z x y : BusbyCycle S J}
    (h : z.IsDirectSum x y) (hz : z.IsUnital) (hx : x.IsUnital) (hy : y.IsUnital) :
    IsUnitarilyEquivalentBusby ((stdCuntzPair J).sumBusby (x.busby hx) (y.busby hy))
      (z.busby hz) := by
  obtain ⟨U, hU, hc⟩ := h
  have hW : (U.comp (Adjointable.adjoint (Adjointable.natSumMerge J))).IsUnitaryAdj :=
    Adjointable.IsUnitaryAdj.comp hU (Adjointable.isUnitaryAdj_natSumMerge J).adjoint
  refine ⟨stdCoronaQuot J (stdBddOfUnitary hW),
    Unitary.map_mem (stdCoronaQuot J) (stdBddOfUnitary_mem hW), fun a => ?_⟩
  have hA : (stdBddOfUnitary hW * (stdCuntzPairBdd J).diag (x.bddLift a) (y.bddLift a)
      * star (stdBddOfUnitary hW)).1
      = Adjointable.comp U (Adjointable.comp (Adjointable.prodMap (x.lift a) (y.lift a))
          (Adjointable.adjoint U)) :=
    adjointable_ext fun v =>
      (congrArg U.toFun (natSumMerge_adj_add
        ((x.lift a).toFun ((Adjointable.natSumMerge J).adj
          ((Adjointable.natSumMerge J).toFun (U.adj v))).1)
        ((y.lift a).toFun ((Adjointable.natSumMerge J).adj
          ((Adjointable.natSumMerge J).toFun (U.adj v))).2))).trans
      (congrArg (fun p : (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J)).carrier =>
          U.toFun ((x.lift a).toFun p.1, (y.lift a).toFun p.2))
        ((Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun (U.adj v)))
  have hq : stdCoronaQuot J (z.bddLift a)
      = stdCoronaQuot J (stdBddOfUnitary hW
          * (stdCuntzPairBdd J).diag (x.bddLift a) (y.bddLift a) * star (stdBddOfUnitary hW)) := by
    refine (stdCoronaQuot_eq_iff _ _).mpr ?_
    rw [hA]
    exact compactEq_symm (hc a)
  rw [map_mul, map_mul, map_star,
    (stdCuntzPairBdd J).map_diag (stdCoronaQuot J) (x.bddLift a) (y.bddLift a)] at hq
  exact hq

/-- **A unital representation as a `⋆`-homomorphism** `S → StdBdd J`. -/
def stdRepHom (ρ : S → StdOp J) (hρ : IsRepresentation (standardModule ℕ J) ρ)
    (h1 : ∀ v, (ρ 1).toFun v = v) : S →⋆ₐ[ℂ] StdBdd J where
  toFun a := ⟨ρ a, mem_boundedAdj.mpr (hρ.bounded a)⟩
  map_one' := Subtype.ext (adjointable_ext h1)
  map_mul' a a' := Subtype.ext (adjointable_ext (hρ.map_mul a a'))
  map_zero' := Subtype.ext (adjointable_ext hρ.map_zero)
  map_add' a a' := Subtype.ext (adjointable_ext (hρ.map_add a a'))
  commutes' c := Subtype.ext (adjointable_ext fun v =>
    ((congrArg (fun s : S => (ρ s).toFun v) (Algebra.algebraMap_eq_smul_one c)).trans
      ((hρ.map_smul c 1 v).trans (congrArg (fun w => c • w) (h1 v)))).trans
      (algebraMap_toFun c v).symm)
  map_star' a := Subtype.ext (adjointable_ext (hρ.map_star a))

theorem stdRepHom_apply (ρ : S → StdOp J) (hρ : IsRepresentation (standardModule ℕ J) ρ)
    (h1 : ∀ v, (ρ 1).toFun v = v) (a : S) : (stdRepHom ρ hρ h1 a).1 = ρ a := rfl

/-- Every `⋆`-homomorphism `S → StdBdd J` is a representation on `H_J`. -/
theorem isRepresentation_starAlgHom (σ : S →⋆ₐ[ℂ] StdBdd J) :
    IsRepresentation (standardModule ℕ J) (fun a => (σ a).1) where
  bounded a := mem_boundedAdj.mp (σ a).2
  map_add a a' v := congrArg (fun T : StdBdd J => T.1.toFun v) (map_add σ a a')
  map_smul c a v := congrArg (fun T : StdBdd J => T.1.toFun v) (map_smul σ c a)
  map_mul a a' v := congrArg (fun T : StdBdd J => T.1.toFun v) (map_mul σ a a')
  map_star a v := congrArg (fun T : StdBdd J => T.1.toFun v) (map_star σ a)

/-- **A cycle split by a unital representation has a trivial Busby map.** -/
theorem BusbyCycle.isTrivialBusby_of_isSplit {x : BusbyCycle S J} (hx : x.IsUnital)
    {ρ : S → StdOp J} (hρ : IsRepresentation (standardModule ℕ J) ρ)
    (h1 : ∀ v, (ρ 1).toFun v = v) (hc : ∀ a : S, CompactEq J (x.lift a) (ρ a)) :
    IsTrivialBusby (stdCoronaQuot J) (x.busby hx) :=
  ⟨stdRepHom ρ hρ h1, fun a =>
    (stdCoronaQuot_eq_iff (stdRepHom ρ hρ h1 a) (x.bddLift a)).mpr (compactEq_symm (hc a))⟩

end Relations

end GroupApproximation.Full.TWWSchafhauser

end
