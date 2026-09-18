import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Words
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-letter residual: other word `a o₁ …` with `o₁ ≠ b` (lane bh-met-77v)

Main word `m = a b c k t`, other word `o = a o₁ o₃` with `o₁ ≠ b`, two letters `a, ā`.  The
root is `T = ([ā], [a, b, c])`; it carries `m ↦ ā k t` and fixes `o`.  The shorter word of the
level-lowering swap is `u = ā u'` with `|u'| ≤ 1` (`higmanVCTauD2_a_u`).

* `v` a prefix of `m` (`higmanVCTauD2_classA_m`): bridge `W = ([a, o₁], [ā])`;
* `v` a prefix of `o` only (`higmanVCTauD2_classA_o`): bridge `W = ([a, b], [ā])`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The shape of `u` when `o = a o₁ o₃` with `o₁ ≠ b`: it starts with the other letter. -/
theorem higmanVCTauD2_a_u {d : ℕ} {a b c k oa o1 : Fin d} {t o3 u v : List (Fin d)}
    (hbina : ∀ e : Fin d, e ≠ a → e = oa) (hbin1 : ∀ e : Fin d, e ≠ b → e = o1)
    (hv3 : v.length ≤ 3) (hlt : u.length < v.length)
    (hum : ¬ u <+: a :: b :: c :: k :: t) (huo : ¬ u <+: a :: o1 :: o3) :
    ∃ u', u = oa :: u' ∧ u'.length ≤ 1 := by
  rcases u with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, u3⟩⟩⟩
  · exact (hum List.nil_prefix).elim
  · by_cases h0 : u0 = a
    · refine (hum ?_).elim
      rw [h0]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
    · exact ⟨[], by rw [hbina u0 h0], by simp⟩
  · by_cases h0 : u0 = a
    · by_cases h1 : u1 = b
      · refine (hum ?_).elim
        rw [h0, h1]
        exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
      · refine (huo ?_).elim
        rw [h0, hbin1 u1 h1]
        exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
    · exact ⟨[u1], by rw [hbina u0 h0], by simp⟩
  · simp only [List.length_cons] at hlt <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_a_u

/-- **Class `o = a o₁ o₃`, `o₁ ≠ b`, `v` a prefix of `m`.**  Bridge `W = ([a, o₁], [ā])`. -/
theorem higmanVCTauD2_classA_m {d : ℕ} {a b c k oa o1 : Fin d}
    {t o3 u' v m' o' : List (Fin d)}
    (hoa : oa ≠ a) (ho1b : o1 ≠ b) (hv3 : v.length ≤ 3) (hu' : u'.length ≤ 1)
    (hlt : u'.length + 1 < v.length) (hvm : v <+: a :: b :: c :: k :: t)
    (hm1 : m' = oa :: u' ++ (a :: b :: c :: k :: t).drop v.length)
    (ho2 : ¬ v <+: a :: o1 :: o3 → o' = a :: o1 :: o3) :
    higmanVCTauD2_Good d [oa] [a, b, c] (a :: b :: c :: k :: t) (a :: o1 :: o3)
      (oa :: u') v m' o' := by
  obtain ⟨v'', hv', -⟩ := higmanVCTauD2_pre2 hvm (by omega)
  have hvl : v.length ≤ t.length + 1 + 1 + 1 + 1 := hvm.length_le
  obtain ⟨hT1, hT2⟩ : ¬ [oa] <+: [a, b, c] ∧ ¬ [a, b, c] <+: [oa] :=
    higmanVCTauBridge_inc_cons [] [b, c] hoa
  obtain ⟨hW1, hW2⟩ : ¬ [a, o1] <+: [oa] ∧ ¬ [oa] <+: [a, o1] :=
    higmanVCTauBridge_inc_cons [o1] [] hoa.symm
  have tM : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: b :: c :: k :: t)
      (oa :: k :: t) := (mapsCone_coneSwap_right hT1 hT2).append (k :: t)
  have tO : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: o1 :: o3) (a :: o1 :: o3) :=
    higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons (o1 :: o3) [] hoa.symm)
      (higmanVCTauD2_inc2 o3 [c] ho1b)
  have wM : MapsCone (coneSwap [a, o1] [oa] hW1 hW2) (a :: b :: c :: k :: t)
      (a :: b :: c :: k :: t) :=
    higmanVCTauD2_fix hW1 hW2 (higmanVCTauD2_inc2 (c :: k :: t) [] ho1b.symm)
      (higmanVCTauBridge_inc_cons (b :: c :: k :: t) [] hoa.symm)
  have wO : MapsCone (coneSwap [a, o1] [oa] hW1 hW2) (a :: o1 :: o3) (oa :: o3) :=
    (mapsCone_coneSwap_left hW1 hW2).append o3
  have wv : MapsCone (coneSwap [a, o1] [oa] hW1 hW2) v v := by
    rw [hv']
    exact higmanVCTauD2_fix hW1 hW2 (higmanVCTauD2_inc2 v'' [] ho1b.symm)
      (higmanVCTauBridge_inc_cons (b :: v'') [] hoa.symm)
  have hvo : ¬ v <+: a :: o1 :: o3 := by
    rw [hv']
    exact (higmanVCTauD2_inc2 v'' o3 ho1b.symm).1
  have e2 := ho2 hvo
  subst e2
  subst hm1
  exact higmanVCTauD2_mkBridge hT1 hT2 (by simp) (by simp) tM tO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    hW1 hW2 (by simp) (by simp) wM wO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    (mapsCone_coneSwap_right hW1 hW2)
    (higmanVCTauD2_fix hW1 hW2 (higmanVCTauD2_inc2 [c] [] ho1b.symm)
      (higmanVCTauBridge_inc_cons [b, c] [] hoa.symm))
    (by simp) (by simp)
    ((mapsCone_coneSwap_right hW1 hW2).append (k :: t)) wO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    ((mapsCone_coneSwap_right hW1 hW2).append u') wv
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega) hv3
    ((mapsCone_coneSwap_right hW1 hW2).append (u' ++ (a :: b :: c :: k :: t).drop v.length))
    wO
    (by
      simp only [List.length_cons, List.length_append, List.length_drop,
        List.length_nil] <;> omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_classA_m
/-- **Class `o = a o₁ o₃`, `o₁ ≠ b`, `v` a prefix of `o` only.**  Bridge `W = ([a, b], [ā])`. -/
theorem higmanVCTauD2_classA_o {d : ℕ} {a b c k oa o1 : Fin d}
    {t o3 u' v m' o' : List (Fin d)}
    (hoa : oa ≠ a) (ho1b : o1 ≠ b) (hv3 : v.length ≤ 3) (hu' : u'.length ≤ 1)
    (hlt : u'.length + 1 < v.length) (hvo : v <+: a :: o1 :: o3)
    (hm2 : m' = a :: b :: c :: k :: t)
    (ho1 : o' = oa :: u' ++ (a :: o1 :: o3).drop v.length) :
    higmanVCTauD2_Good d [oa] [a, b, c] (a :: b :: c :: k :: t) (a :: o1 :: o3)
      (oa :: u') v m' o' := by
  obtain ⟨v'', hv', -⟩ := higmanVCTauD2_pre2 hvo (by omega)
  have hvl : v.length ≤ o3.length + 1 + 1 := hvo.length_le
  obtain ⟨hT1, hT2⟩ : ¬ [oa] <+: [a, b, c] ∧ ¬ [a, b, c] <+: [oa] :=
    higmanVCTauBridge_inc_cons [] [b, c] hoa
  obtain ⟨hW1, hW2⟩ : ¬ [a, b] <+: [oa] ∧ ¬ [oa] <+: [a, b] :=
    higmanVCTauBridge_inc_cons [b] [] hoa.symm
  have tM : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: b :: c :: k :: t)
      (oa :: k :: t) := (mapsCone_coneSwap_right hT1 hT2).append (k :: t)
  have tO : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: o1 :: o3) (a :: o1 :: o3) :=
    higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons (o1 :: o3) [] hoa.symm)
      (higmanVCTauD2_inc2 o3 [c] ho1b)
  have wM : MapsCone (coneSwap [a, b] [oa] hW1 hW2) (a :: b :: c :: k :: t)
      (oa :: c :: k :: t) := (mapsCone_coneSwap_left hW1 hW2).append (c :: k :: t)
  have wO : MapsCone (coneSwap [a, b] [oa] hW1 hW2) (a :: o1 :: o3) (a :: o1 :: o3) :=
    higmanVCTauD2_fix hW1 hW2 (higmanVCTauD2_inc2 o3 [] ho1b)
      (higmanVCTauBridge_inc_cons (o1 :: o3) [] hoa.symm)
  have wv : MapsCone (coneSwap [a, b] [oa] hW1 hW2) v v := by
    rw [hv']
    exact higmanVCTauD2_fix hW1 hW2 (higmanVCTauD2_inc2 v'' [] ho1b)
      (higmanVCTauBridge_inc_cons (o1 :: v'') [] hoa.symm)
  subst hm2
  subst ho1
  exact higmanVCTauD2_mkBridge hT1 hT2 (by simp) (by simp) tM tO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    hW1 hW2 (by simp) (by simp) wM wO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    (mapsCone_coneSwap_right hW1 hW2) ((mapsCone_coneSwap_left hW1 hW2).append [c])
    (by simp) (by simp)
    ((mapsCone_coneSwap_right hW1 hW2).append (k :: t)) wO
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)
    ((mapsCone_coneSwap_right hW1 hW2).append u') wv
    (by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega) hv3
    wM ((mapsCone_coneSwap_right hW1 hW2).append (u' ++ (a :: o1 :: o3).drop v.length))
    (by
      simp only [List.length_cons, List.length_append, List.length_drop,
        List.length_nil] <;> omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_classA_o

/-- **Class `o = a o₁ o₃`, `o₁ ≠ b`.**  The swap `(u v)` is reached by a bridge. -/
theorem higmanVCTauD2_classA {d : ℕ} {a b c k oa o1 : Fin d}
    {t o3 u v m' o' : List (Fin d)}
    (hoa : oa ≠ a) (ho1b : o1 ≠ b) (hbina : ∀ e : Fin d, e ≠ a → e = oa)
    (hbin1 : ∀ e : Fin d, e ≠ b → e = o1)
    (hUV : higmanVCTauD2_UV d u v (a :: b :: c :: k :: t) (a :: o1 :: o3) m' o') :
    higmanVCTauD2_Good d [oa] [a, b, c] (a :: b :: c :: k :: t) (a :: o1 :: o3) u v m' o' := by
  obtain ⟨hv3, hlt, hum, huo, hvmo, hm1, hm2, ho1, ho2⟩ := hUV
  obtain ⟨u', rfl, hu'⟩ := higmanVCTauD2_a_u hbina hbin1 hv3 hlt hum huo
  have hlt' : u'.length + 1 < v.length := hlt
  by_cases hvm : v <+: a :: b :: c :: k :: t
  · exact higmanVCTauD2_classA_m hoa ho1b hv3 hu' hlt' hvm (hm1 hvm) ho2
  · have hvo : v <+: a :: o1 :: o3 := hvmo.resolve_left hvm
    exact higmanVCTauD2_classA_o hoa ho1b hv3 hu' hlt' hvo (hm2 hvm) (ho1 hvo)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_classA

end GroupApproximation.BooneHigman.Metabelian.Envelope
