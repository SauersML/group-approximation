import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlEqlen
import GroupApproximation.Meta.AxiomGuard

/-!
# A long word forces flexible A or B on three letters (lane bh-met-77z)

Let `σ = (p q)` with `|p|, |q| ≤ 3`.  Let `m ↦ m'` and `o ↦ o'` under `σ`, with `|m| ≥ 4`,
`o` not a prefix of `m`, and `|m'| + |o'| = |m| + |o|.  On `d ≥ 3` letters,
`higmanVCTauEqLvl_core` shows that the pair `(m, o)` has flexible A for `σ` or flexible B
towards `(m', o')`.
* `higmanVCTauEqLvl_coreM`: `m` lies in the cone of a swapped word `a`.  If `o` is in the cone
  of the other word `b` and `|a| ≥ 2` or `|b| ≥ 2`, flexible B comes from
  `higmanVCTauEqLvl_t3`.  Otherwise `|a| = |b|`, and flexible A comes from
  `higmanVCTauEqLvl_eqlen`.
* `higmanVCTauEqLvl_coreF`: `σ` fixes `m`, and flexible A comes from the template at
  `P = m[0..3)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A prefix of `m` is not a prefix of a word `a` that is not a prefix of `m`, when `|a| ≤ |P|`. -/
theorem higmanVCTauEqLvl_not_prefix_short {d : ℕ} {P a m : List (Fin d)} (hPm : P <+: m)
    (ham : ¬ a <+: m) (ha : a.length ≤ P.length) : ¬ P <+: a := fun h => ham (by
  have e := h.eq_of_length (Nat.le_antisymm h.length_le ha)
  rw [← e]
  exact hPm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_not_prefix_short

/-- **`m` in the cone of `a`.** -/
theorem higmanVCTauEqLvl_coreM {d : ℕ} (hd : 3 ≤ d) {σ : Equiv.Perm (Cantor (Fin d))}
    {a b u o o' : List (Fin d)} (hs : higmanVCTauEqLvl_Sw σ a b) (ha3 : a.length ≤ 3)
    (hb3 : b.length ≤ 3) (hm : 4 ≤ (a ++ u).length) (hom : ¬ o <+: a ++ u)
    (ho : MapsCone σ o o')
    (hlen : (b ++ u).length + o'.length = (a ++ u).length + o.length) :
    higmanVCTauEqLvl_FA σ (a ++ u) o ∨ higmanVCTauComm_FlexB d a b (a ++ u) o (b ++ u) o' ∨
      higmanVCTauComm_FlexB d b a o (a ++ u) o' (b ++ u) := by
  have hs' := hs
  obtain ⟨hab, hba, -, -, -, -⟩ := hs'
  have ha1 := higmanVCTauEqLvl_len_pos hab
  have hb1 := higmanVCTauEqLvl_len_pos hba
  have ham : a <+: a ++ u := List.prefix_append a u
  simp only [List.length_append] at hm
  rcases higmanVCTauEqLvl_cases (by omega) hs ho with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ |
    ⟨-, -, -, -, rfl⟩
  · simp only [List.length_append] at hlen
    exact Or.inl (higmanVCTauEqLvl_eqlen hd hs ha3 (by omega)
      (by simp only [List.length_append]; omega) ham hom ho
      (by simp only [List.length_append]; omega))
  · by_cases h2 : 2 ≤ a.length
    · exact Or.inr (Or.inl (higmanVCTauEqLvl_t3 hd u v hab hba h2 ha3 hb3))
    by_cases h2' : 2 ≤ b.length
    · exact Or.inr (Or.inr (higmanVCTauEqLvl_t3 hd v u hba hab h2' hb3 ha3))
    exact Or.inl (higmanVCTauEqLvl_eqlen hd hs ha3 (by omega)
      (by simp only [List.length_append]; omega) ham hom ho
      (by simp only [List.length_append]; omega))
  · simp only [List.length_append] at hlen
    exact Or.inl (higmanVCTauEqLvl_eqlen hd hs ha3 (by omega)
      (by simp only [List.length_append]; omega) ham hom ho (Nat.le_refl _))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_coreM

/-- **`m` fixed.** -/
theorem higmanVCTauEqLvl_coreF {d : ℕ} (hd : 3 ≤ d) {σ : Equiv.Perm (Cantor (Fin d))}
    {a b m o o' : List (Fin d)} (hs : higmanVCTauEqLvl_Sw σ a b) (ha3 : a.length ≤ 3)
    (hb3 : b.length ≤ 3) (hm : 4 ≤ m.length) (ham : ¬ a <+: m) (hbm : ¬ b <+: m)
    (hom : ¬ o <+: m) (ho : MapsCone σ o o') (ho'l : o'.length ≤ o.length) :
    higmanVCTauEqLvl_FA σ m o := by
  obtain ⟨-, -, -, -, -, hfix⟩ := hs
  rcases m with _ | ⟨m0, _ | ⟨m1, _ | ⟨m2, R⟩⟩⟩
  · simp at hm
  · simp at hm
  · simp at hm
  have hPm : [m0, m1, m2] <+: m0 :: m1 :: m2 :: R := ⟨R, rfl⟩
  have h1m : [m0] <+: m0 :: m1 :: m2 :: R := ⟨m1 :: m2 :: R, rfl⟩
  have hP3 : [m0, m1, m2].length = 3 := rfl
  have hoP : ¬ o <+: [m0, m1, m2] := fun h => hom (h.trans hPm)
  have haP : ¬ a <+: [m0, m1, m2] := fun h => ham (h.trans hPm)
  have hbP : ¬ b <+: [m0, m1, m2] := fun h => hbm (h.trans hPm)
  have hPa := higmanVCTauEqLvl_not_prefix_short hPm ham (by omega)
  have hPb := higmanVCTauEqLvl_not_prefix_short hPm hbm (by omega)
  obtain ⟨Q, hQl, ⟨hQP, hPQ⟩, ⟨hQa, haQ⟩, ⟨hQb, hbQ⟩, ⟨hQo, hoQ⟩⟩ :=
    higmanVCTauEqLvl_Q hd m0 m1 [m2] a b o (fun h => ham (h.trans h1m))
      (fun h => hbm (h.trans h1m)) (fun h => hom (h.trans h1m))
  exact higmanVCTauEqLvl_tmpl (P := [m0, m1, m2]) (R := R) rfl hoP hQl hQP hPQ hQo hoQ
    (hfix _ hPa haP hPb hbP) (by simp) (hfix Q hQa haQ hQb hbQ) hQl ho ho'l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_coreF

end GroupApproximation.BooneHigman.Metabelian.Envelope
