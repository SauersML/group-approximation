import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Cone-swap identities behind the short relators of `V_d` (lane bh-met-77)

Permutation-level facts used to place the standard relator families of the short cone swaps in
the relator set `higmanVFPRelators d` (`EnvelopeHigmanVFPBall.lean`).

* `higmanVFP_coneSwap_comm`: `(v w) = (w v)`, checked pointwise on `cone v`, `cone w` and the
  rest of the boundary.
* `higmanVFP_ne_letter`, `higmanVFP_ext_incomp`: one-letter extensions of incomparable words, and
  distinct one-letter extensions of one word, are incomparable.
* `higmanVFPSplitSwap h1 h2 a = (va wa)` and its fixed cones `v b`, `w b` for `b ≠ a`
  (`vgen_mapsCone_coneSwap_fix`), feeding the split relation `(v w) = ∏ₐ (va wa)` proved in
  `EnvelopeHigmanVFPSplit.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- **Symmetry of cone swaps.**  `(v w) = (w v)`. -/
theorem higmanVFP_coneSwap_comm {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) :
    coneSwap v w h1 h2 = coneSwap w v h2 h1 := by
  refine Equiv.ext fun x => ?_
  show coneSwapFun v w x = coneSwapFun w v x
  by_cases hv : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hv
    rw [coneSwapFun_prepend_left, coneSwapFun_prepend_right h2 h1]
  · by_cases hw : IsStreamPrefix w x
    · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hw
      rw [coneSwapFun_prepend_right h1 h2, coneSwapFun_prepend_left]
    · rw [coneSwapFun_of_not hv hw, coneSwapFun_of_not hw hv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_coneSwap_comm

/-- Distinct one-letter extensions of a word are incomparable. -/
theorem higmanVFP_ne_letter (u : List X) {a b : X} (hab : a ≠ b) : ¬ (u ++ [a]) <+: (u ++ [b]) :=
  fun h => hab (List.cons_prefix_cons.mp ((List.prefix_append_right_inj u).mp h)).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_ne_letter

/-- One-letter extensions of incomparable words are incomparable. -/
theorem higmanVFP_ext_incomp {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (a b : X) :
    ¬ (v ++ [a]) <+: (w ++ [b]) :=
  vgen_not_prefix_append_left [a] (vgen_not_prefix_append_right [b] h2 h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_ext_incomp

/-- The factor `(va wa)` of the split relation for `(v w)`. -/
noncomputable def higmanVFPSplitSwap {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (a : X) :
    Equiv.Perm (Cantor X) :=
  coneSwap (v ++ [a]) (w ++ [a]) (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPSplitSwap

/-- The split factors of `(v w)` and of `(w v)` agree. -/
theorem higmanVFPSplitSwap_comm {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (a : X) :
    higmanVFPSplitSwap h1 h2 a = higmanVFPSplitSwap h2 h1 a :=
  higmanVFP_coneSwap_comm (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPSplitSwap_comm

/-- A stream is its first letter followed by its tail. -/
theorem higmanVFP_prepend_head (y : Cantor X) : prepend [y 0] (dropN 1 y) = y :=
  prepend_dropN_of_isStreamPrefix [y 0] y fun k hk => by
    obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
    rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_prepend_head

/-- For `b ≠ a` the factor `(va wa)` fixes the cone `v b` pointwise. -/
theorem higmanVFPSplitSwap_fixLeft {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) {a b : X}
    (hab : a ≠ b) : MapsCone (higmanVFPSplitSwap h1 h2 a) (v ++ [b]) (v ++ [b]) :=
  vgen_mapsCone_coneSwap_fix (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a)
    (higmanVFP_ne_letter v hab.symm) (higmanVFP_ne_letter v hab)
    (higmanVFP_ext_incomp h1 h2 b a) (higmanVFP_ext_incomp h2 h1 a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPSplitSwap_fixLeft

/-- For `b ≠ a` the factor `(va wa)` fixes the cone `w b` pointwise. -/
theorem higmanVFPSplitSwap_fixRight {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) {a b : X}
    (hab : a ≠ b) : MapsCone (higmanVFPSplitSwap h1 h2 a) (w ++ [b]) (w ++ [b]) :=
  vgen_mapsCone_coneSwap_fix (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a)
    (higmanVFP_ext_incomp h2 h1 b a) (higmanVFP_ext_incomp h1 h2 a b)
    (higmanVFP_ne_letter w hab.symm) (higmanVFP_ne_letter w hab)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPSplitSwap_fixRight

end GroupApproximation.BooneHigman.Metabelian.Envelope
