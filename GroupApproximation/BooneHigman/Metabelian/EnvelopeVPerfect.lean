import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfectSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll
import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsion
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import GroupApproximation.Meta.AxiomGuard

/-!
# `V_Y` is perfect when `|Y|` is even

This proves `GenTorsionVPerfectStatement` outright (`genTorsionVPerfect`), with no hypotheses.

Route. Let `Y` be finite with `|Y|` even, `V = higmanThompsonV Y` and `cls(a, b)` the class of
the cone swap `s(a, b)` in `Vᵃᵇ`.
1. `s(v, w) = ∏_y s(vy, wy)` (`vPerfectChain_eq_coneSwap`, file `EnvelopeVPerfectSplit.lean`).
2. `cls(b, c) = cls(a, c)` for pairwise incomparable `a, b, c` (conjugate by `s(a, b)`), and
   `cls(a, b) = cls(b, a)`. Hence all children `cls(vy, wy)` equal one class `c`
   (`vPerfect_child_eq`).
3. `c ^ 2 = 1`, so `cls(v, w) = c ^ |Y| = (c ^ 2) ^ (|Y| / 2) = 1`, and `s(v, w) ∈ ⁅V, V⁆`
   (`vPerfect_coneSwap_mem`).
4. The cone swaps generate `V` (`swapGen_mem_of_coneSwap_mem`), so `V ≤ ⁅V, V⁆`. For
   `Y = Fin 2 × X`, `|Y| = 2 |X|` is even.

Corollaries: `RNGeneratorTorsionStatement` and `RNCommutatorFiniteIndexStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*} [Finite X] {v w : List X}

/-- All children of `s(v, w)` have one class in `Vᵃᵇ`. -/
theorem vPerfect_child_eq (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y y' : X) :
    vPerfectCls (vPerfect_inc_cross hvw hwv y y) (vPerfect_inc_cross hwv hvw y y) =
      vPerfectCls (vPerfect_inc_cross hvw hwv y' y') (vPerfect_inc_cross hwv hvw y' y') := by
  by_cases h : y = y'
  · subst h
    rfl
  · exact (vPerfectCls_move (vPerfect_inc_letter v (Ne.symm h)) (vPerfect_inc_letter v h)
        (vPerfect_inc_cross hvw hwv y' y) (vPerfect_inc_cross hwv hvw y y')
        (vPerfect_inc_cross hvw hwv y y) (vPerfect_inc_cross hwv hvw y y)).trans
      ((vPerfectCls_symm (vPerfect_inc_cross hvw hwv y' y)
        (vPerfect_inc_cross hwv hvw y y')).trans
      ((vPerfectCls_move (vPerfect_inc_letter w (Ne.symm h)) (vPerfect_inc_letter w h)
        (vPerfect_inc_cross hwv hvw y' y') (vPerfect_inc_cross hvw hwv y' y')
        (vPerfect_inc_cross hwv hvw y y') (vPerfect_inc_cross hvw hwv y' y)).trans
      (vPerfectCls_symm (vPerfect_inc_cross hwv hvw y' y') (vPerfect_inc_cross hvw hwv y' y'))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_child_eq

/-- The chain over `L` has class `cls ^ L.length`. -/
theorem vPerfectChain_cls (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y₀ : X) : ∀ L : List X,
    (Abelianization.of : ↥(higmanThompsonV X) →* Abelianization ↥(higmanThompsonV X))
        (vPerfectChain hvw hwv L) =
      vPerfectCls (vPerfect_inc_cross hvw hwv y₀ y₀) (vPerfect_inc_cross hwv hvw y₀ y₀) ^
        L.length
  | [] => by rw [vPerfectChain_nil, map_one, List.length_nil, pow_zero]
  | y :: L => by
    rw [vPerfectChain_cons, map_mul, vPerfectChain_cls hvw hwv y₀ L, List.length_cons,
      pow_succ']
    congr 1
    exact vPerfect_child_eq hvw hwv y y₀

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_cls

/-- When `|X|` is even, every cone swap lies in `⁅V, V⁆`. -/
theorem vPerfect_coneSwap_mem [Nonempty X] (heven : Even (Nat.card X)) (hvw : ¬ v <+: w)
    (hwv : ¬ w <+: v) : coneSwap v w hvw hwv ∈ ⁅higmanThompsonV X, higmanThompsonV X⁆ := by
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨y₀⟩ : Nonempty X := inferInstance
  have hsplit := vPerfectChain_eq_coneSwap hvw hwv (Finset.univ : Finset X).toList
    (Finset.nodup_toList _) (fun y => Finset.mem_toList.mpr (Finset.mem_univ y))
  have hlen : (Finset.univ : Finset X).toList.length = Nat.card X := by
    rw [Finset.length_toList, Finset.card_univ, Nat.card_eq_fintype_card]
  have hc : (Abelianization.of : ↥(higmanThompsonV X) →* Abelianization ↥(higmanThompsonV X))
      (vPerfectChain hvw hwv (Finset.univ : Finset X).toList) = 1 := by
    obtain ⟨k, hk⟩ := heven
    rw [vPerfectChain_cls hvw hwv y₀, hlen, hk, ← two_mul, pow_mul, vPerfectCls_sq, one_pow]
  have hmem : vPerfectChain hvw hwv (Finset.univ : Finset X).toList ∈
      commutator ↥(higmanThompsonV X) :=
    (Abelianization.ker_of ↥(higmanThompsonV X)).le (MonoidHom.mem_ker.mpr hc)
  have e := Subgroup.mem_map_of_mem (higmanThompsonV X).subtype hmem
  rw [Subgroup.map_subtype_commutator] at e
  rw [← hsplit]
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_coneSwap_mem

/-- When `|X|` is even, Higman's `V_X` is perfect. -/
theorem vPerfect_higmanThompsonV_le [Nontrivial X] (heven : Even (Nat.card X)) :
    higmanThompsonV X ≤ ⁅higmanThompsonV X, higmanThompsonV X⁆ := by
  intro _ hf
  exact swapGen_mem_of_coneSwap_mem (fun _ _ h1 h2 => vPerfect_coneSwap_mem heven h1 h2) hf

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_higmanThompsonV_le

/-- **`GenTorsionVPerfectStatement` holds**: `V_{Fin 2 × X}` is perfect. -/
theorem genTorsionVPerfect : GenTorsionVPerfectStatement := by
  intro X _ _
  refine vPerfect_higmanThompsonV_le ?_
  show Even (Nat.card (Fin 2 × X))
  rw [Nat.card_prod, Nat.card_fin]
  exact ⟨Nat.card X, two_mul _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.genTorsionVPerfect

theorem vPerfect_rnGeneratorTorsion : RNGeneratorTorsionStatement :=
  rnGeneratorTorsion_of_vPerfect genTorsionVPerfect

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_rnGeneratorTorsion

theorem vPerfect_rnFiniteIndex : RNCommutatorFiniteIndexStatement :=
  rnFiniteIndex_of_vPerfect genTorsionVPerfect

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_rnFiniteIndex

end GroupApproximation.BooneHigman.Metabelian.Envelope
