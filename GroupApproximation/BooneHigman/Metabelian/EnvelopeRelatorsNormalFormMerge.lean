import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: merging two factor lists with compatible words

Two words are *compatible* when they are equal or incomparable.
* `rnNF_insert`: suppose the new factor `rfConjL e k` has a word `w` compatible with every word
  of `P`.  Then `Π P * rfConjL e k = Π P'` for a factor list `P'` whose words lie in
  `{w} ∪ words P`.  If some factor of `P` sits on the same cone, the new factor commutes past the
  later factors, which are incomparable with `w`, and is absorbed into it.  Otherwise it is
  pushed further in.
* `rnNF_merge`: `Π P * Π Q = Π P'` when every word of `P` is compatible with every word of `Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X] [Nontrivial X]

/-- **Inserting one factor.** -/
theorem rnNF_insert (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (hdisj : nfDisjRelators H x₀ ⊆ N)
    (e : ↥(higmanThompsonV X)) (w : List X) (k : ↥H)
    (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w) :
    ∀ P : List (↥(higmanThompsonV X) × List X × ↥H),
      (∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) →
      P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
      (∀ p ∈ P, p.2.1 = w ∨ (¬ p.2.1 <+: w ∧ ¬ w <+: p.2.1)) →
      ∃ P' : List (↥(higmanThompsonV X) × List X × ↥H),
        (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (∀ b ∈ P', b.2.1 = w ∨ ∃ p ∈ P, b.2.1 = p.2.1) ∧
        (P.map fun p => rfConjL H N p.1 p.2.2).prod * rfConjL H N e k =
          (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  intro P
  induction P with
  | nil =>
    intro _ _ _
    refine ⟨[(e, w, k)], fun a ha => ?_, List.pairwise_singleton _ _, fun b hb => ?_, ?_⟩
    · rw [List.mem_singleton.mp ha]
      exact he
    · rw [List.mem_singleton.mp hb]
      exact Or.inl rfl
    · simp only [List.map_nil, List.prod_nil, one_mul, List.map_cons, List.prod_cons, mul_one]
  | cons p P ih =>
    intro hv hpair hcw
    rw [List.pairwise_cons] at hpair
    rcases hcw p List.mem_cons_self with hpw | hpw
    · have hcP : Commute (rfConjL H N e k) (P.map fun p => rfConjL H N p.1 p.2.2).prod :=
        Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
          have hi := hpair.1 q hq
          rw [hpw] at hi
          exact rcore_commute_rfConjL_incomp H N x₀ hcomm hdisj hi.1 hi.2 he
            (hv q (List.mem_cons_of_mem p hq)) k q.2.2
      have hep : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] p.2.1 := by
        rw [hpw]
        exact he
      refine ⟨(p.1, p.2.1, p.2.2 * k) :: P, fun a ha => ?_,
        List.Pairwise.cons (fun b hb => hpair.1 b hb) hpair.2, fun b hb => ?_, ?_⟩
      · rcases List.mem_cons.mp ha with h | ha
        · rw [h]
          exact hv p List.mem_cons_self
        · exact hv a (List.mem_cons_of_mem p ha)
      · rcases List.mem_cons.mp hb with h | hb
        · rw [h]
          exact Or.inl hpw
        · exact Or.inr ⟨b, List.mem_cons_of_mem p hb, rfl⟩
      · simp only [List.map_cons, List.prod_cons]
        rw [mul_assoc, ← hcP.eq, ← mul_assoc,
          rnNF_rfConjL_mul_same H N x₀ hcomm (hv p List.mem_cons_self) hep p.2.2 k]
    · obtain ⟨P₀, hv₀, hp₀, hw₀, he₀⟩ :=
        ih (fun q hq => hv q (List.mem_cons_of_mem p hq)) hpair.2
          (fun q hq => hcw q (List.mem_cons_of_mem p hq))
      refine ⟨p :: P₀, fun a ha => ?_, List.Pairwise.cons (fun b hb => ?_) hp₀,
        fun b hb => ?_, ?_⟩
      · rcases List.mem_cons.mp ha with h | ha
        · rw [h]
          exact hv p List.mem_cons_self
        · exact hv₀ a ha
      · rcases hw₀ b hb with hbw | ⟨q, hq, hbq⟩
        · rw [hbw]
          exact hpw
        · rw [hbq]
          exact hpair.1 q hq
      · rcases List.mem_cons.mp hb with h | hb
        · rw [h]
          exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
        · rcases hw₀ b hb with hbw | ⟨q, hq, hbq⟩
          · exact Or.inl hbw
          · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, hbq⟩
      · simp only [List.map_cons, List.prod_cons]
        rw [mul_assoc, he₀]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_insert

/-- **Merging two factor lists with compatible words.** -/
theorem rnNF_merge (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (hdisj : nfDisjRelators H x₀ ⊆ N) :
    ∀ Q : List (↥(higmanThompsonV X) × List X × ↥H),
      (∀ q ∈ Q, MapsCone (q.1 : Equiv.Perm (Cantor X)) [x₀] q.2.1) →
      Q.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
      ∀ P : List (↥(higmanThompsonV X) × List X × ↥H),
      (∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) →
      P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
      (∀ p ∈ P, ∀ q ∈ Q, p.2.1 = q.2.1 ∨ (¬ p.2.1 <+: q.2.1 ∧ ¬ q.2.1 <+: p.2.1)) →
      ∃ P' : List (↥(higmanThompsonV X) × List X × ↥H),
        (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (P.map fun p => rfConjL H N p.1 p.2.2).prod * (Q.map fun q => rfConjL H N q.1 q.2.2).prod =
          (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  intro Q
  induction Q with
  | nil =>
    intro _ _ P hvP hpP _
    exact ⟨P, hvP, hpP, by simp only [List.map_nil, List.prod_nil, mul_one]⟩
  | cons q Q ih =>
    intro hvQ hpQ P hvP hpP hPQ
    rw [List.pairwise_cons] at hpQ
    obtain ⟨P₁, hv₁, hp₁, hw₁, he₁⟩ := rnNF_insert H N x₀ hcomm hdisj q.1 q.2.1 q.2.2
      (hvQ q List.mem_cons_self) P hvP hpP fun p hp => hPQ p hp q List.mem_cons_self
    obtain ⟨P', hv', hp', he'⟩ := ih (fun r hr => hvQ r (List.mem_cons_of_mem q hr)) hpQ.2 P₁
      hv₁ hp₁ fun b hb r hr => by
        rcases hw₁ b hb with hbq | ⟨p, hp, hbp⟩
        · rw [hbq]
          exact Or.inr (hpQ.1 r hr)
        · rw [hbp]
          exact hPQ p hp r (List.mem_cons_of_mem q hr)
    refine ⟨P', hv', hp', ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, he₁, he']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_merge

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
