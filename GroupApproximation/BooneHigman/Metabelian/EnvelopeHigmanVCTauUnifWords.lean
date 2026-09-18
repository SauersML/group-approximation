import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDeepReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Incomparable words for the uniform deep witnesses (lane bh-met-77y)

`higmanVCTauUnif_Inc u w` says that neither of `u`, `w` is a prefix of the other.  The lemmas
here are the word bookkeeping of the uniform Hop D / Hop CD witnesses
(`EnvelopeHigmanVCTauUnifHop`): incomparability survives appending on either side, distinct
one-letter extensions are incomparable, a cone swap fixes a word incomparable with both of its
words, and the pair facts for a "shape" pair `{z, zo} = {p0, q0}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Two words are incomparable: neither is a prefix of the other. -/
abbrev higmanVCTauUnif_Inc (u w : List X) : Prop := ¬ u <+: w ∧ ¬ w <+: u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_Inc

theorem higmanVCTauUnif_incS {u w : List X} (h : higmanVCTauUnif_Inc u w) :
    higmanVCTauUnif_Inc w u :=
  ⟨h.2, h.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_incS

theorem higmanVCTauUnif_incL {u w : List X} (c : List X) (h : higmanVCTauUnif_Inc u w) :
    higmanVCTauUnif_Inc (u ++ c) w :=
  ⟨vgen_not_prefix_append_left c h.1, vgen_not_prefix_append_right c h.1 h.2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_incL

theorem higmanVCTauUnif_incR {u w : List X} (c : List X) (h : higmanVCTauUnif_Inc u w) :
    higmanVCTauUnif_Inc u (w ++ c) :=
  higmanVCTauUnif_incS (higmanVCTauUnif_incL c (higmanVCTauUnif_incS h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_incR

theorem higmanVCTauUnif_incB {u w : List X} (c e : List X) (h : higmanVCTauUnif_Inc u w) :
    higmanVCTauUnif_Inc (u ++ c) (w ++ e) :=
  higmanVCTauUnif_incR e (higmanVCTauUnif_incL c h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_incB

/-- Distinct one-letter extensions of a word are incomparable. -/
theorem higmanVCTauUnif_inc_letter (u : List X) {a b : X} (hab : a ≠ b) :
    higmanVCTauUnif_Inc (u ++ [a]) (u ++ [b]) :=
  ⟨higmanVFP_ne_letter u hab, higmanVFP_ne_letter u (Ne.symm hab)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_inc_letter

/-- Words with distinct first letters are incomparable. -/
theorem higmanVCTauUnif_inc_cons {a b : X} (hab : a ≠ b) (l l' : List X) :
    higmanVCTauUnif_Inc (a :: l) (b :: l') :=
  ⟨fun h => hab (List.cons_prefix_cons.mp h).1, fun h => hab (List.cons_prefix_cons.mp h).1.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_inc_cons

/-- A common prefix does not change incomparability. -/
theorem higmanVCTauUnif_inc_pre (u : List X) {l l' : List X} (h : higmanVCTauUnif_Inc l l') :
    higmanVCTauUnif_Inc (u ++ l) (u ++ l') :=
  ⟨fun h' => h.1 ((List.prefix_append_right_inj u).mp h'),
    fun h' => h.2 ((List.prefix_append_right_inj u).mp h')⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_inc_pre

/-- A cone swap fixes the cone of a word incomparable with both of its words. -/
theorem higmanVCTauUnif_fix {v w u : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v)
    (h1 : higmanVCTauUnif_Inc u v) (h2 : higmanVCTauUnif_Inc u w) :
    MapsCone (coneSwap v w hvw hwv) u u :=
  vgen_mapsCone_coneSwap_fix hvw hwv h1.1 h1.2 h2.1 h2.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_fix

/-- Length of a word with one marked letter. -/
theorem higmanVCTauUnif_len1 (z : List X) (c : X) : (z ++ [c]).length = z.length + 1 := by
  have e1 : (z ++ [c]).length = z.length + [c].length := List.length_append
  have e2 : [c].length = 1 := rfl
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_len1

/-- Length of a word `z c t`. -/
theorem higmanVCTauUnif_len3 (z : List X) (c : X) (t : List X) :
    (z ++ [c] ++ t).length = z.length + t.length + 1 := by
  have e1 : (z ++ [c] ++ t).length = (z ++ [c]).length + t.length := List.length_append
  have e2 := higmanVCTauUnif_len1 z c
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_len3

/-- The word `a e` has length two. -/
theorem higmanVCTauUnif_len_qa (a e : X) : ([a] ++ [e]).length = 2 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_len_qa

end GroupApproximation.BooneHigman.Metabelian.Envelope
