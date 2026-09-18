import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a cone swap into its one-letter children

Route to `GenTorsionVPerfectStatement` (file `EnvelopeVPerfect.lean`), step 1. Take incomparable
words `v`, `w`. For a letter `y`, the child swap `s(vy, wy)` exchanges the cones of `v ++ [y]` and
`w ++ [y]`. `vPerfectChain hvw hwv L` is the product of the child swaps over a list `L` of letters.

* `vPerfectChain_fix`: the chain fixes every stream outside the cones of its children;
* `vPerfectChain_maps`: when `L` has no duplicates, the chain carries `cone (v ++ [y])` onto
  `cone (w ++ [y])` and back, for every `y ∈ L`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- One-letter extensions of incomparable words stay incomparable. -/
theorem vPerfect_inc_cross {v w : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y y' : X) :
    ¬ (v ++ [y]) <+: (w ++ [y']) :=
  vgen_not_prefix_append_left [y] (vgen_not_prefix_append_right [y'] hwv hvw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_inc_cross

/-- Distinct one-letter extensions of one word are incomparable. -/
theorem vPerfect_inc_letter (v : List X) {y y' : X} (h : y ≠ y') :
    ¬ (v ++ [y]) <+: (v ++ [y']) :=
  fun hp => not_prefix_cons_of_ne h [] [] ((List.prefix_append_right_inj v).mp hp)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_inc_letter

/-- A stream in the cone of `b` does not begin with a word `a` incomparable with `b`. -/
theorem vPerfect_not_isStreamPrefix {a b : List X} (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (z : Cantor X) : ¬ IsStreamPrefix a (prepend b z) :=
  fun h => Set.disjoint_left.mp (disjoint_cone hab hba) h (prepend_mem_cone b z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_not_isStreamPrefix

/-- Every stream is its first letter followed by the rest. -/
theorem vPerfect_prepend_head (z : Cantor X) : prepend [z 0] (dropN 1 z) = z := by
  have h : IsStreamPrefix [z 0] z := by
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp
  exact prepend_dropN_of_isStreamPrefix [z 0] z h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfect_prepend_head

variable [Finite X] {v w : List X}

/-- The child swap `s(v ++ [y], w ++ [y])`, as an element of `V`. -/
noncomputable def vPerfectChild (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y : X) :
    ↥(higmanThompsonV X) :=
  ⟨coneSwap (v ++ [y]) (w ++ [y]) (vPerfect_inc_cross hvw hwv y y)
    (vPerfect_inc_cross hwv hvw y y), coneSwap_mem_higmanThompsonV _ _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChild

/-- The product of the child swaps over a list of letters. -/
noncomputable def vPerfectChain (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    List X → ↥(higmanThompsonV X)
  | [] => 1
  | y :: L => vPerfectChild hvw hwv y * vPerfectChain hvw hwv L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain

theorem vPerfectChain_nil (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    vPerfectChain hvw hwv [] = 1 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_nil

theorem vPerfectChain_cons (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y : X) (L : List X) :
    vPerfectChain hvw hwv (y :: L) = vPerfectChild hvw hwv y * vPerfectChain hvw hwv L := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_cons

theorem vPerfectChain_cons_coe (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y : X) (L : List X) :
    (vPerfectChain hvw hwv (y :: L) : Equiv.Perm (Cantor X)) =
      coneSwap (v ++ [y]) (w ++ [y]) (vPerfect_inc_cross hvw hwv y y)
        (vPerfect_inc_cross hwv hvw y y) * (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_cons_coe

/-- The chain fixes every stream outside the cones of its children. -/
theorem vPerfectChain_fix (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) : ∀ (L : List X) (x : Cantor X),
    (∀ y ∈ L, ¬ IsStreamPrefix (v ++ [y]) x ∧ ¬ IsStreamPrefix (w ++ [y]) x) →
      (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) x = x
  | [], _, _ => rfl
  | y :: L, x, h => by
    rw [vPerfectChain_cons_coe, Equiv.Perm.mul_apply,
      vPerfectChain_fix hvw hwv L x (fun y' hy' => h y' (List.mem_cons_of_mem y hy')),
      coneSwap_apply]
    exact coneSwapFun_of_not (h y List.mem_cons_self).1 (h y List.mem_cons_self).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_fix

/-- A chain avoiding the letter `y` fixes the cone of `v ++ [y]`. -/
theorem vPerfectChain_fix_left (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) {L : List X} {y : X}
    (hyL : y ∉ L) :
    MapsCone (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) (v ++ [y]) (v ++ [y]) := by
  intro z
  refine vPerfectChain_fix hvw hwv L _ fun y' hy' => ⟨?_, ?_⟩
  · have hne : y ≠ y' := fun h => hyL (by rw [h]; exact hy')
    exact vPerfect_not_isStreamPrefix (vPerfect_inc_letter v (Ne.symm hne))
      (vPerfect_inc_letter v hne) z
  · exact vPerfect_not_isStreamPrefix (vPerfect_inc_cross hwv hvw y' y)
      (vPerfect_inc_cross hvw hwv y y') z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_fix_left

/-- A chain avoiding the letter `y` fixes the cone of `w ++ [y]`. -/
theorem vPerfectChain_fix_right (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) {L : List X} {y : X}
    (hyL : y ∉ L) :
    MapsCone (vPerfectChain hvw hwv L : Equiv.Perm (Cantor X)) (w ++ [y]) (w ++ [y]) := by
  intro z
  refine vPerfectChain_fix hvw hwv L _ fun y' hy' => ⟨?_, ?_⟩
  · exact vPerfect_not_isStreamPrefix (vPerfect_inc_cross hvw hwv y' y)
      (vPerfect_inc_cross hwv hvw y y') z
  · have hne : y ≠ y' := fun h => hyL (by rw [h]; exact hy')
    exact vPerfect_not_isStreamPrefix (vPerfect_inc_letter w (Ne.symm hne))
      (vPerfect_inc_letter w hne) z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectChain_fix_right

end GroupApproximation.BooneHigman.Metabelian.Envelope
