import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetComap

/-!
# Homotopy invariance of `Ext(-, J)`: the elementary reductions

Lane `TWWSch3d3-3C1`, work order `WO-TWWSch3d3-3C` §3C1. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378). The Rosenberg–Schochet comparison used there needs
homotopic `⋆`-homomorphisms out of a nuclear source to induce the same map on `Ext(-, J)`
(G. G. Kasparov, Izv. Akad. Nauk SSSR 44 (1980), §7; B. Blackadar, *K-theory for operator
algebras*, 15.8 and 17.6).

This file has the parts that need no analysis.

* `ExtGroup.mk_eq_of_compactEq`: **compact perturbation**, the case `U = 1` of unitary
  equivalence.
* `ExtGroup.comap_eq_of_forall_mk`: two pull-backs agree once they agree on cycle classes.
* `BusbyCycle.compactEq_lift_sub`: a lift is additive on differences modulo compacts.
* `BusbyCycle.exists_compact_opNorm_sub_sub_le`: an essential-norm bound for `x.lift (b - b')`
  is one for `x.lift b - x.lift b'`.
* `BusbyCycle.IsEssNormContinuousPath`: a path of cycles whose Busby maps `A → Q(J ⊗ 𝒦)` are
  pointwise norm-continuous in the corona norm `inf_K ‖T - K‖`. This is the hypothesis of the
  Kasparov homotopy core.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Basic

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Cycles whose lifts agree modulo compacts are unitarily equivalent, via `U = 1`
(`thm:fixed-radical-membership`). -/
theorem BusbyCycle.isUnitarilyEquivalent_of_compactEq {x y : BusbyCycle A J}
    (h : ∀ a : A, CompactEq J (x.lift a) (y.lift a)) : x.IsUnitarilyEquivalent y :=
  ⟨Adjointable.id (standardModule ℕ J), Adjointable.isUnitaryAdj_id (standardModule ℕ J),
    fun a =>
      Adjointable.IsCompactOp.congr
        (T := Adjointable.sub (x.lift a) (y.lift a))
        (T' := Adjointable.sub
          (Adjointable.comp (Adjointable.id (standardModule ℕ J))
            (Adjointable.comp (x.lift a)
              (Adjointable.adjoint (Adjointable.id (standardModule ℕ J)))))
          (y.lift a))
        (fun _ => rfl) (h a)⟩

/-- **Compact perturbation.** Cycles whose lifts agree modulo compacts have the same class
(`thm:fixed-radical-membership`). -/
theorem ExtGroup.mk_eq_of_compactEq {x y : BusbyCycle A J}
    (h : ∀ a : A, CompactEq J (x.lift a) (y.lift a)) : ExtGroup.mk x = ExtGroup.mk y :=
  ExtGroup.mk_eq_of_isUnitarilyEquivalent (BusbyCycle.isUnitarilyEquivalent_of_compactEq h)

/-- Two pull-backs `f^*, g^* : Ext(B, J) → Ext(A, J)` agree once they agree on the classes of
cycles (`thm:fixed-radical-membership`). -/
theorem ExtGroup.comap_eq_of_forall_mk {f g : A →⋆ₙₐ[ℂ] B}
    (h : ∀ x : BusbyCycle B J, ExtGroup.mk (x.comap f) = ExtGroup.mk (x.comap g)) :
    (ExtGroup.comap f : ExtGroup B J →+ ExtGroup A J) = ExtGroup.comap g :=
  ExtGroup.hom_ext fun x =>
    (ExtGroup.comap_mk f x).trans ((h x).trans (ExtGroup.comap_mk g x).symm)

/-- A lift is additive on differences modulo compacts: `x(b - b') ≡ x(b) - x(b')`. -/
theorem BusbyCycle.compactEq_lift_sub (x : BusbyCycle A J) (b b' : A) :
    CompactEq J (x.lift (b - b')) (Adjointable.sub (x.lift b) (x.lift b')) := by
  have hb : b - b' = b + (-1 : ℂ) • b' := by
    rw [neg_one_smul ℂ b', sub_eq_add_neg]
  rw [hb]
  exact Adjointable.IsCompactOp.congr
    (T := Adjointable.add
      (Adjointable.sub (x.lift (b + (-1 : ℂ) • b'))
        (Adjointable.add (x.lift b) (x.lift ((-1 : ℂ) • b'))))
      (Adjointable.sub (x.lift ((-1 : ℂ) • b')) (Adjointable.smul (-1) (x.lift b'))))
    (T' := Adjointable.sub (x.lift (b + (-1 : ℂ) • b')) (Adjointable.sub (x.lift b) (x.lift b')))
    (fun v => by
      show (x.lift (b + (-1 : ℂ) • b')).toFun v -
            ((x.lift b).toFun v + (x.lift ((-1 : ℂ) • b')).toFun v) +
          ((x.lift ((-1 : ℂ) • b')).toFun v - (-1 : ℂ) • (x.lift b').toFun v) =
        (x.lift (b + (-1 : ℂ) • b')).toFun v - ((x.lift b).toFun v - (x.lift b').toFun v)
      rw [neg_one_smul ℂ ((x.lift b').toFun v)]
      abel)
    (Adjointable.IsCompactOp.add
      (T := Adjointable.sub (x.lift (b + (-1 : ℂ) • b'))
        (Adjointable.add (x.lift b) (x.lift ((-1 : ℂ) • b'))))
      (S := Adjointable.sub (x.lift ((-1 : ℂ) • b')) (Adjointable.smul (-1) (x.lift b')))
      (x.map_add b ((-1 : ℂ) • b')) (x.map_smul (-1) b'))

/-- Operators with the same underlying map: the operator norm of the second is at most that of
the first. -/
theorem stdOp_opNorm_le_of_toFun_eq {T T' : StdOp J} (h : ∀ v, T.toFun v = T'.toFun v)
    (hT : T.IsBounded) : T'.opNorm ≤ T.opNorm := by
  refine Adjointable.opNorm_le_of_bound (Adjointable.opNorm_nonneg T) ?_
  intro v
  show (standardModule ℕ J).norm (T'.toFun v) ≤ T.opNorm * (standardModule ℕ J).norm v
  rw [← h v]
  exact Adjointable.norm_apply_le_opNorm hT v

/-- **Essential-norm transfer.** A compact `K` with `‖x(b - b') - K‖ ≤ r` gives a compact `K'`
with `‖(x(b) - x(b')) - K'‖ ≤ r`, namely `K' = K - (x(b - b') - (x(b) - x(b')))`. -/
theorem BusbyCycle.exists_compact_opNorm_sub_sub_le (x : BusbyCycle A J) (b b' : A)
    {K : StdOp J} (hK : K.IsCompactOp) {r : ℝ}
    (h : (Adjointable.sub (x.lift (b - b')) K).opNorm ≤ r) :
    ∃ K' : StdOp J, K'.IsCompactOp ∧
      (Adjointable.sub (Adjointable.sub (x.lift b) (x.lift b')) K').opNorm ≤ r := by
  refine ⟨Adjointable.sub K
      (Adjointable.sub (x.lift (b - b')) (Adjointable.sub (x.lift b) (x.lift b'))),
    Adjointable.IsCompactOp.sub hK (x.compactEq_lift_sub b b'), ?_⟩
  obtain ⟨C, hC, hCb⟩ := x.bounded (b - b')
  obtain ⟨D, hD, hDb⟩ := hK.isBounded
  refine le_trans (stdOp_opNorm_le_of_toFun_eq
    (T := Adjointable.sub (x.lift (b - b')) K)
    (T' := Adjointable.sub (Adjointable.sub (x.lift b) (x.lift b'))
      (Adjointable.sub K
        (Adjointable.sub (x.lift (b - b')) (Adjointable.sub (x.lift b) (x.lift b')))))
    (fun v => ?_) ⟨C + D, add_nonneg hC hD, hCb.sub hDb⟩) h
  show (x.lift (b - b')).toFun v - K.toFun v =
    ((x.lift b).toFun v - (x.lift b').toFun v) -
      (K.toFun v - ((x.lift (b - b')).toFun v - ((x.lift b).toFun v - (x.lift b').toFun v)))
  abel

/-- **Essential-norm continuous path of cycles.** For every `a`, the operators `x(t)(a)` depend
continuously on `t` modulo compacts: near `t₀`, `x(t)(a) - x(t₀)(a)` is within `ε` of a compact
operator. Equivalently the Busby maps `A → Q(J ⊗ 𝒦)` form a pointwise norm-continuous path, i.e.
a `⋆`-homomorphism `A → C(ℝ, Q(J ⊗ 𝒦))` (`thm:fixed-radical-membership`). -/
def BusbyCycle.IsEssNormContinuousPath (x : ℝ → BusbyCycle A J) : Prop :=
  ∀ (a : A) (t₀ ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ →
    ∃ K : StdOp J, K.IsCompactOp ∧
      (Adjointable.sub (Adjointable.sub ((x t).lift a) ((x t₀).lift a)) K).opNorm ≤ ε

end Basic

end GroupApproximation.Full.TWWSchafhauser
