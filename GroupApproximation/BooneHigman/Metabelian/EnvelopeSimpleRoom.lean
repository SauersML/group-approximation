import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleEpstein
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import GroupApproximation.BooneHigman.V.Transitive
import GroupApproximation.Meta.AxiomGuard

/-!
# Room around cones, and nontriviality of `[V_X(H), V_X(H)]`

* `threeRoom_cone`: for letters `a ≠ b` and any word `u`, the cone swaps of `V_X` give room
  `ThreeRoom (roverNekrashevych X H) (cone u) (cone (u ++ [a, a]))`, with further parts
  `cone (u ++ [a, b])` and `cone (u ++ [b])`.
* `commutator_rn_ne_bot`: for `Nontrivial X` the commutator of the swaps `[a] ↔ [b]` and
  `[a, a] ↔ [a, b]` is not `1`: at `aa·y` one order gives `bb·y`, the other `ba·y`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

variable {X : Type*}

theorem not_isStreamPrefix_cons_prepend {a b : X} (hab : a ≠ b) (l w : List X) (z : Cantor X) :
    ¬ IsStreamPrefix (a :: l) (prepend (b :: w) z) := by
  intro h
  have h0 := h 0 (by simp)
  rw [prepend_getElem (b :: w) z (n := 0) (by simp), List.getElem_cons_zero,
    List.getElem_cons_zero] at h0
  exact hab h0.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.not_isStreamPrefix_cons_prepend

theorem not_prefix_append_of_ne {a b : X} (hab : a ≠ b) (u l w : List X) :
    ¬ (u ++ a :: l) <+: (u ++ b :: w) := fun h =>
  not_prefix_cons_of_ne hab l w ((List.prefix_append_right_inj u).mp h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.not_prefix_append_of_ne

theorem threeRoom_cone [Finite X] (H : Subgroup (TreeAut X)) (u : List X) {a b : X}
    (hab : a ≠ b) : ThreeRoom (roverNekrashevych X H) (cone u) (cone (u ++ [a, a])) := by
  have p12 : ¬ (u ++ [a, a]) <+: (u ++ [a, b]) := fun h =>
    not_prefix_cons_of_ne hab [] []
      (List.cons_prefix_cons.mp ((List.prefix_append_right_inj u).mp h)).2
  have p21 : ¬ (u ++ [a, b]) <+: (u ++ [a, a]) := fun h =>
    not_prefix_cons_of_ne hab.symm [] []
      (List.cons_prefix_cons.mp ((List.prefix_append_right_inj u).mp h)).2
  have p13 : ¬ (u ++ [a, a]) <+: (u ++ [b]) := not_prefix_append_of_ne hab u [a] []
  have p31 : ¬ (u ++ [b]) <+: (u ++ [a, a]) := not_prefix_append_of_ne hab.symm u [] [a]
  have p23 : ¬ (u ++ [a, b]) <+: (u ++ [b]) := not_prefix_append_of_ne hab u [b] []
  have p32 : ¬ (u ++ [b]) <+: (u ++ [a, b]) := not_prefix_append_of_ne hab.symm u [] [b]
  refine ⟨cone (u ++ [a, b]), cone (u ++ [b]), coneSwap _ _ p12 p21,
    higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV p12 p21), coneSwap _ _ p13 p31,
    higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV p13 p31), ?_, ?_,
    disjoint_cone p12 p21, disjoint_cone p13 p31, disjoint_cone p23 p32, ?_⟩
  · intro x hx
    rw [← (mapsCone_coneSwap_left p12 p21).image_cone]
    exact hx
  · intro x hx
    rw [← (mapsCone_coneSwap_left p13 p31).image_cone]
    exact hx
  · exact Set.union_subset (Set.union_subset (cone_append_subset u [a, a])
      (cone_append_subset u [a, b])) (cone_append_subset u [b])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.threeRoom_cone

theorem commutator_rn_ne_bot [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)) :
    ⁅roverNekrashevych X H, roverNekrashevych X H⁆ ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have p1 : ¬ [a] <+: [b] := not_prefix_cons_of_ne hab [] []
  have p2 : ¬ [b] <+: [a] := not_prefix_cons_of_ne hab.symm [] []
  have p12 : ¬ [a, a] <+: [a, b] := fun h => p1 (List.cons_prefix_cons.mp h).2
  have p21 : ¬ [a, b] <+: [a, a] := fun h => p2 (List.cons_prefix_cons.mp h).2
  have hs := higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV p1 p2)
  have ht := higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV p12 p21)
  intro hbot
  have h1 := Subgroup.commutator_mem_commutator hs ht
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have y : Cantor X := fun _ => a
  have h2 := congrArg (fun g : Equiv.Perm (Cantor X) => g (prepend [a, a] y)) h1
  simp only [Equiv.Perm.mul_apply, coneSwap_apply] at h2
  have e1 : prepend [a, a] y = prepend [a] (prepend [a] y) := prepend_append [a] [a] y
  have e2 : prepend [a, b] y = prepend [a] (prepend [b] y) := prepend_append [a] [b] y
  rw [coneSwapFun_prepend_left [a, a] [a, b] y, e2,
    coneSwapFun_prepend_left [a] [b] (prepend [b] y), e1, coneSwapFun_prepend_left [a] [b] (prepend [a] y),
    coneSwapFun_of_not (not_isStreamPrefix_cons_prepend hab [a] [] (prepend [a] y))
      (not_isStreamPrefix_cons_prepend hab [b] [] (prepend [a] y))] at h2
  have h3 := prepend_injective [b] h2
  have h4 := isStreamPrefix_prepend [a] y
  rw [← h3] at h4
  exact not_isStreamPrefix_cons_prepend hab [] [] y h4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutator_rn_ne_bot

end GroupApproximation.BooneHigman.Metabelian.Envelope
