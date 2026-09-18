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

/-- The word `a e` against `u c`, when `u` does not start with `a`. -/
theorem higmanVCTauUnif_qaL {a e : X} {u : List X} (c : X) (h : higmanVCTauUnif_Inc [a] u) :
    higmanVCTauUnif_Inc ([a] ++ [e]) (u ++ [c]) :=
  higmanVCTauUnif_incB [e] [c] h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_qaL

/-- The word `u b` against `a e`, when `u` does not start with `a`. -/
theorem higmanVCTauUnif_qaR {a e : X} {u : List X} (b : X) (h : higmanVCTauUnif_Inc [a] u) :
    higmanVCTauUnif_Inc (u ++ [b]) ([a] ++ [e]) :=
  higmanVCTauUnif_incB [b] [e] (higmanVCTauUnif_incS h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_qaR

/-- The word `a t0'` (with `t0' ≠ t0`) against `a t0 t1`. -/
theorem higmanVCTauUnif_qaT {d : ℕ} (hd : 1 < d) (a t0 : Fin d) (t1 : List (Fin d)) :
    higmanVCTauUnif_Inc ([a] ++ [higmanVCTau_other t0]) ([a] ++ (t0 :: t1)) :=
  higmanVCTauUnif_inc_pre [a] (higmanVCTauUnif_inc_cons (higmanVCTauConj_other_ne hd t0) [] t1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_qaT

/-- Facts on a shape pair `{z, zo} = {p0, q0}`. -/
theorem higmanVCTauUnif_pair {a : X} {z zo p0 q0 : List X} (hz : z.length = 2)
    (hzo : zo.length = 2) (hzz : higmanVCTauUnif_Inc z zo) (haz : higmanVCTauUnif_Inc [a] z)
    (hazo : higmanVCTauUnif_Inc [a] zo) (hw : (z = p0 ∧ zo = q0) ∨ (z = q0 ∧ zo = p0)) :
    higmanVCTauUnif_Inc p0 q0 ∧ higmanVCTauUnif_Inc [a] p0 ∧ higmanVCTauUnif_Inc [a] q0 ∧
      p0.length = 2 ∧ q0.length = 2 := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hzz, haz, hazo, hz, hzo⟩
  · exact ⟨higmanVCTauUnif_incS hzz, hazo, haz, hzo, hz⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_pair

/-- The swap of a shape pair exchanges `z` and `zo`. -/
theorem higmanVCTauUnif_maps_pair {z zo p0 q0 : List X} (h0 : ¬ p0 <+: q0) (h0' : ¬ q0 <+: p0)
    (hw : (z = p0 ∧ zo = q0) ∨ (z = q0 ∧ zo = p0)) :
    MapsCone (coneSwap p0 q0 h0 h0') z zo ∧ MapsCone (coneSwap p0 q0 h0 h0') zo z := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨mapsCone_coneSwap_left h0 h0', mapsCone_coneSwap_right h0 h0'⟩
  · exact ⟨mapsCone_coneSwap_right h0 h0', mapsCone_coneSwap_left h0 h0'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_maps_pair

/-- A marked word `z c` is incomparable with both sibling words `p0 b`, `q0 b` (`b ≠ c`). -/
theorem higmanVCTauUnif_sib {b c : X} {z zo p0 q0 : List X} (hcb : c ≠ b)
    (hzz : higmanVCTauUnif_Inc z zo) (hw : (z = p0 ∧ zo = q0) ∨ (z = q0 ∧ zo = p0)) :
    higmanVCTauUnif_Inc (z ++ [c]) (p0 ++ [b]) ∧ higmanVCTauUnif_Inc (z ++ [c]) (q0 ++ [b]) := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨higmanVCTauUnif_inc_letter _ hcb, higmanVCTauUnif_incB [c] [b] hzz⟩
  · exact ⟨higmanVCTauUnif_incB [c] [b] hzz, higmanVCTauUnif_inc_letter _ hcb⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_sib

end GroupApproximation.BooneHigman.Metabelian.Envelope
