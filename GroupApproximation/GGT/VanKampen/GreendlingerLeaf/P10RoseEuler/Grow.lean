import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.Extract
import GroupApproximation.Meta.AxiomGuard

/-!
# Growing a closed trail through a connected balanced list

* `exists_touch`: let `W` be a closed trail and `R` a nonempty remainder, with `W ++ R` a
  permutation of `L`, where any two entries of `L` are joined by a chain of entries sharing a
  vertex.  Then some entry `b` of `R` has a vertex (start or end) that is the start of an entry `w`
  of `W`.  Proof: walk the chain from the first entry of `W` to the first entry of `R`.  As long
  as the chain stays in `W`, a step to an entry of `R` gives the touching pair (every end label of
  a closed trail is also a start label, `IsClosedTrail.exists_start_eq_end`).  If the chain never
  leaves `W`, the first entry of `R` itself lies in `W`.
* `exists_perm_closedTrail_grow`: Hierholzer's growth step, by strong induction on `R.length`.
  Extract a closed trail `C` from the balanced remainder through the touching entry `b`, merge it
  into `W` at the shared vertex (`IsClosedTrail.join`), and recurse on what is left.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler

section Generic

variable {α V : Type*} {s t : α → V}

/-- **A remainder touches the trail.**  If the entries of `L` are connected through shared
vertices and `W ++ R` is a permutation of `L` with `W` a closed trail and `R ≠ []`, some entry of
`R` has a vertex that starts an entry of `W`. -/
theorem exists_touch {L W R : List α} (hW : IsClosedTrail s t W) (hperm : (W ++ R).Perm L)
    (hR : R ≠ [])
    (hconn : ∀ d ∈ L, ∀ e ∈ L, Relation.ReflTransGen
      (fun a b => a ∈ L ∧ b ∈ L ∧ (t a = s b ∨ s b = t a ∨ s a = s b ∨ t a = t b)) d e) :
    ∃ b ∈ R, ∃ w ∈ W, s w = s b ∨ s w = t b := by
  have hW0 : W ≠ [] := hW.ne_nil
  have hinv : ∀ c : α, Relation.ReflTransGen
      (fun a b => a ∈ L ∧ b ∈ L ∧ (t a = s b ∨ s b = t a ∨ s a = s b ∨ t a = t b))
      (W.head hW0) c → (∃ b ∈ R, ∃ w ∈ W, s w = s b ∨ s w = t b) ∨ c ∈ W := by
    intro c hc
    induction hc with
    | refl => exact Or.inr (List.head_mem hW0)
    | tail _ hab ih =>
      rcases ih with h | ha
      · exact Or.inl h
      · obtain ⟨_, hbL, hrel⟩ := hab
        rcases List.mem_append.mp (hperm.mem_iff.mpr hbL) with hbW | hbR
        · exact Or.inr hbW
        · refine Or.inl ⟨_, hbR, ?_⟩
          rcases hrel with h1 | h1 | h1 | h1
          · obtain ⟨w, hw, hsw⟩ := hW.exists_start_eq_end ha
            exact ⟨w, hw, Or.inl (hsw.trans h1)⟩
          · obtain ⟨w, hw, hsw⟩ := hW.exists_start_eq_end ha
            exact ⟨w, hw, Or.inl (hsw.trans h1.symm)⟩
          · exact ⟨_, ha, Or.inl h1⟩
          · obtain ⟨w, hw, hsw⟩ := hW.exists_start_eq_end ha
            exact ⟨w, hw, Or.inr (hsw.trans h1)⟩
  have hstart : W.head hW0 ∈ L :=
    hperm.mem_iff.mp (List.mem_append_left R (List.head_mem hW0))
  have hend : R.head hR ∈ L :=
    hperm.mem_iff.mp (List.mem_append_right W (List.head_mem hR))
  rcases hinv (R.head hR) (hconn (W.head hW0) hstart (R.head hR) hend) with h | h
  · exact h
  · exact ⟨R.head hR, List.head_mem hR, R.head hR, h, Or.inl rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_touch

/-- **Hierholzer's growth step.**  A closed trail `W` together with a balanced remainder `R`, with
`W ++ R` a permutation of a connected list `L`, grows to a closed trail that is a permutation
of `L`. -/
theorem exists_perm_closedTrail_grow [DecidableEq V] {L : List α}
    (hconn : ∀ d ∈ L, ∀ e ∈ L, Relation.ReflTransGen
      (fun a b => a ∈ L ∧ b ∈ L ∧ (t a = s b ∨ s b = t a ∨ s a = s b ∨ t a = t b)) d e) :
    ∀ (n : ℕ) (W R : List α), R.length = n → IsClosedTrail s t W → (W ++ R).Perm L →
      IsBalanced s t R → ∃ L' : List α, L'.Perm L ∧ IsClosedTrail s t L' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W R hlen hW hperm hbal
    by_cases hR : R = []
    · subst hR
      rw [List.append_nil] at hperm
      exact ⟨W, hperm, hW⟩
    · obtain ⟨b, hb, w, hw, hwb⟩ := exists_touch hW hperm hR hconn
      obtain ⟨C, R', hC0, hC, hhead, hCperm⟩ := exists_closedTrail_head hbal hb
      have hbC : b ∈ C := by
        rw [← hhead]
        exact List.head_mem hC0
      have hc : ∃ c ∈ C, s w = s c := by
        rcases hwb with h | h
        · exact ⟨b, hbC, h⟩
        · obtain ⟨c, hc, hsc⟩ := hC.exists_start_eq_end hbC
          exact ⟨c, hc, h.trans hsc.symm⟩
      obtain ⟨c, hc, hwc⟩ := hc
      obtain ⟨J, hJperm, hJ⟩ := hW.join hC hw hc hwc
      have hbal' : IsBalanced s t R' :=
        IsBalanced.cancel_left (hbal.perm hCperm.symm) hC.isBalanced
      have hlen' : R'.length < n := by
        have h1 : (C ++ R').length = R.length := hCperm.length_eq
        have h2 : (C ++ R').length = C.length + R'.length := List.length_append
        have h3 : 0 < C.length := List.length_pos_iff.mpr hC0
        omega
      have hperm' : (J ++ R').Perm L := by
        have h1 : (J ++ R').Perm (W ++ C ++ R') := List.Perm.append_right R' hJperm
        have h2 : (W ++ C ++ R').Perm (W ++ R) := by
          rw [List.append_assoc]
          exact List.Perm.append_left W hCperm
        exact h1.trans (h2.trans hperm)
      exact ih R'.length hlen' J R' rfl hJ hperm' hbal'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_perm_closedTrail_grow

end Generic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler
