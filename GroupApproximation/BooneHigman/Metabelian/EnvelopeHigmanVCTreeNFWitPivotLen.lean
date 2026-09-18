import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivot
import GroupApproximation.Meta.AxiomGuard

/-!
# Antichain words with a balanced image preserve lengths (lane bh-met-77p)

Let `C` be a finite antichain and `r` a word in the transpositions of `C`.  Suppose the class
of `ι_C r` has the same `E`-image as some `β ∈ U`.  Then the permutation `σ` of `C` read off
from `r` preserves word lengths: `|σ c| = |c|` for every `c ∈ C`.

Proof: `β` lies in the balanced group on all words of some length `L ≥ |c|`.  Pad `c` to a
word `c ++ e₀` of length `L`.  The element `E(ι_C r)` maps the cone of `c ++ e₀` onto the cone
of `σ c ++ e₀` (antichain cone mapping), and onto the cone of a word of length `L` (the balanced
cone mapping for `β`).  Cone images are unique, so `|σ c| + |e₀| = L = |c| + |e₀|`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTreeNFWitPivot_len {d : ℕ} (hd : 1 < d) {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (r : FreeGroup (↥C × ↥C)) {β : higmanVCCommon_Q d}
    (hβ : β ∈ higmanVCTreeNF_U d)
    (e : higmanVCTreeNF_E d (higmanVCCommon_mk d (higmanVCAll_iota C r)) =
      higmanVCTreeNF_E d β)
    (c : ↥C) :
    (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c).1.length = c.1.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨M, hM⟩ := higmanVCTreeNF_mem_U.mp hβ
  obtain ⟨L, hML, hcL⟩ : ∃ L : ℕ, M ≤ L ∧ c.1.length ≤ L :=
    ⟨M + c.1.length, by omega, by omega⟩
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (higmanVCTreeNF_range_mono hML hM)
  obtain ⟨e0, he0⟩ : ∃ e0 : List (Fin d), c.1.length + e0.length = L :=
    ⟨List.replicate (L - c.1.length) ⟨0, by omega⟩, by rw [List.length_replicate]; omega⟩
  have hw : c.1 ++ e0 ∈ higmanVCCentral_words d L :=
    (higmanVCCentral_mem_words_iff d L _).mpr (by rw [List.length_append]; omega)
  have hs' : higmanVCCommon_mk d (higmanVCAll_iota (higmanVCCentral_words d L) s) = β := hs
  have e1 := e
  rw [← hs'] at e1
  have e2 : higmanVC_evalAll d (higmanVCAll_iota C r) =
      higmanVC_evalAll d (higmanVCAll_iota (higmanVCCentral_words d L) s) := e1
  have h1 := (higmanVCAll_mapsCone_word hC r c).append e0
  have h2 := higmanVCAll_mapsCone_word (higmanVCCentral_words_antichain d L) s ⟨c.1 ++ e0, hw⟩
  rw [← e2] at h2
  have key : ∀ v : ↥(higmanVCCentral_words d L),
      (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c).1 ++ e0 = v.1 →
        (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c).1.length =
          c.1.length := by
    intro v hv
    have h7 := (higmanVCCentral_mem_words_iff d L v.1).mp v.2
    have h8 := congrArg List.length hv
    rw [List.length_append] at h8
    omega
  exact key _ (MapsCone.unique h1 h2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_len

end GroupApproximation.BooneHigman.Metabelian.Envelope
