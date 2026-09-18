import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Words
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-letter residual: other word `a b o₂ …` (lane bh-met-77v)

Main word `m = a b c k t`, other word `o = a b o₂ o₄`, two letters `a, ā` and `b, b̄`.  The
root is `T = ([ā], [a, b, c])`.  With no fresh word, the shorter word of the level-lowering
swap is `u = [a, b̄]` (`higmanVCTauD2_ab_u`), so `|v| = 3`, and `T` gives a direct edge into
`(u, v)` (`higmanVCTauD2_classAB`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The shape of `u` when `[a, b̄]` is comparable with `u`. -/
theorem higmanVCTauD2_ab_u {d : ℕ} {a b c k ob : Fin d} {t u v : List (Fin d)}
    (hbinb : ∀ e : Fin d, e ≠ b → e = ob) (hv3 : v.length ≤ 3) (hlt : u.length < v.length)
    (hum : ¬ u <+: a :: b :: c :: k :: t)
    (hF : (¬ [a, ob] <+: u ∧ ¬ u <+: [a, ob]) → False) : u = [a, ob] := by
  rcases u with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, u3⟩⟩⟩
  · exact (hum List.nil_prefix).elim
  · by_cases h0 : u0 = a
    · refine (hum ?_).elim
      rw [h0]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
    · exact (hF (higmanVCTauBridge_inc_cons [ob] [] (Ne.symm h0))).elim
  · by_cases h0 : u0 = a
    · by_cases h1 : u1 = b
      · refine (hum ?_).elim
        rw [h0, h1]
        exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
      · rw [h0, hbinb u1 h1]
    · exact (hF (higmanVCTauBridge_inc_cons [ob] [u1] (Ne.symm h0))).elim
  · simp only [List.length_cons] at hlt <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_ab_u

/-- The root `T = ([ā], [a, b, c])` does not lengthen `o = a b o₂ o₄`. -/
theorem higmanVCTauD2_ab_rootO {d : ℕ} {a b c oa o2 : Fin d} {o4 : List (Fin d)}
    (hoa : oa ≠ a) (hT1 : ¬ [oa] <+: [a, b, c]) (hT2 : ¬ [a, b, c] <+: [oa]) :
    ∃ Y0 : List (Fin d), MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: b :: o2 :: o4) Y0 ∧
      Y0.length ≤ (a :: b :: o2 :: o4).length := by
  by_cases h2 : o2 = c
  · subst h2
    exact ⟨oa :: o4, (mapsCone_coneSwap_right hT1 hT2).append o4, by
      simp only [List.length_cons] <;> omega⟩
  · have hi : ¬ a :: b :: o2 :: o4 <+: [a, b, c] ∧ ¬ [a, b, c] <+: a :: b :: o2 :: o4 :=
      higmanVCTauD2_inc_tail a (higmanVCTauD2_inc_tail b (higmanVCTauBridge_inc_cons o4 [] h2))
    exact ⟨a :: b :: o2 :: o4,
      higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons (b :: o2 :: o4) [] hoa.symm) hi,
      le_refl _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_ab_rootO

/-- **Class `o = a b o₂ o₄`.**  With no fresh word the root gives a direct edge into the
swap `(u v)`. -/
theorem higmanVCTauD2_classAB {d : ℕ} {a b c k oa ob o2 : Fin d}
    {t o4 u v m' o' : List (Fin d)}
    (hoa : oa ≠ a) (hob : ob ≠ b) (hbinb : ∀ e : Fin d, e ≠ b → e = ob)
    (hUV : higmanVCTauD2_UV d u v (a :: b :: c :: k :: t) (a :: b :: o2 :: o4) m' o')
    (hNF : higmanVCTauD2_NF d [oa] [a, b, c] (a :: b :: c :: k :: t) (a :: b :: o2 :: o4) u v) :
    higmanVCTauD2_Good d [oa] [a, b, c] (a :: b :: c :: k :: t) (a :: b :: o2 :: o4)
      u v m' o' := by
  obtain ⟨hv3, hlt, hum, huo, hvmo, hm1, hm2, ho1, ho2⟩ := hUV
  have hu1 : 1 ≤ u.length := by
    rcases u with _ | ⟨u0, u'⟩
    · exact (hum List.nil_prefix).elim
    · simp
  have hv2 : 2 ≤ v.length := by omega
  have hvab : ∃ v'' : List (Fin d), v = a :: b :: v'' := by
    rcases hvmo with h | h
    · obtain ⟨v'', e, -⟩ := higmanVCTauD2_pre2 h hv2
      exact ⟨v'', e⟩
    · obtain ⟨v'', e, -⟩ := higmanVCTauD2_pre2 h hv2
      exact ⟨v'', e⟩
  obtain ⟨v'', hv'⟩ := hvab
  have hu : u = [a, ob] := higmanVCTauD2_ab_u hbinb hv3 hlt hum (fun hF => by
    unfold higmanVCTauD2_NF at hNF
    refine hNF [a, ob] (by simp) (higmanVCTauBridge_inc_cons [ob] [] hoa.symm)
      (higmanVCTauD2_inc2 [] [c] hob) (higmanVCTauD2_inc2 [] (c :: k :: t) hob)
      (higmanVCTauD2_inc2 [] (o2 :: o4) hob) hF ?_
    rw [hv']
    exact higmanVCTauD2_inc2 [] v'' hob)
  subst hu
  have hv : v.length = 3 := by
    simp only [List.length_cons, List.length_nil] at hlt
    omega
  obtain ⟨hT1, hT2⟩ : ¬ [oa] <+: [a, b, c] ∧ ¬ [a, b, c] <+: [oa] :=
    higmanVCTauBridge_inc_cons [] [b, c] hoa
  have fixAB : ∀ r : List (Fin d),
      MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: ob :: r) (a :: ob :: r) := fun r =>
    higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons (ob :: r) [] hoa.symm)
      (higmanVCTauD2_inc2 r [c] hob)
  have tM : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) (a :: b :: c :: k :: t)
      (oa :: k :: t) := (mapsCone_coneSwap_right hT1 hT2).append (k :: t)
  obtain ⟨Y0, tO, hY0⟩ := higmanVCTauD2_ab_rootO (o2 := o2) (o4 := o4) hoa hT1 hT2
  have ht : (oa :: k :: t).length + Y0.length <
      (a :: b :: c :: k :: t).length + (a :: b :: o2 :: o4).length := by
    simp only [List.length_cons] at hY0 ⊢ <;> omega
  have hP : [oa].length ≤ 3 := by simp
  have hQ : [a, b, c].length ≤ 3 := by simp
  have hu2 : [a, ob].length ≤ 3 := by simp
  have tu : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) [a, ob] [a, ob] := fixAB []
  by_cases hvm : v <+: a :: b :: c :: k :: t
  · obtain rfl := higmanVCTauD2_pre3 hvm hv
    have e1 : m' = [a, ob] ++ (a :: b :: c :: k :: t).drop [a, b, c].length := hm1 hvm
    subst e1
    by_cases hvo : [a, b, c] <+: a :: b :: o2 :: o4
    · have e2 : o' = [a, ob] ++ (a :: b :: o2 :: o4).drop [a, b, c].length := ho1 hvo
      subst e2
      exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tu
        (mapsCone_coneSwap_right hT1 hT2) hu2 hP
        (fixAB ((a :: b :: c :: k :: t).drop [a, b, c].length))
        (fixAB ((a :: b :: o2 :: o4).drop [a, b, c].length))
        (by
          simp only [List.length_cons, List.length_append, List.length_drop,
            List.length_nil] <;> omega)
    · have e2 : o' = a :: b :: o2 :: o4 := ho2 hvo
      subst e2
      exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tu
        (mapsCone_coneSwap_right hT1 hT2) hu2 hP
        (fixAB ((a :: b :: c :: k :: t).drop [a, b, c].length)) tO
        (by
          simp only [List.length_cons, List.length_append, List.length_drop,
            List.length_nil] at hY0 ⊢ <;> omega)
  · have hvo : v <+: a :: b :: o2 :: o4 := hvmo.resolve_left hvm
    obtain rfl := higmanVCTauD2_pre3 hvo hv
    have ho2c : o2 ≠ c := fun h => hvm (by
      rw [h]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl,
        List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩⟩)
    have hi : ¬ [a, b, o2] <+: [a, b, c] ∧ ¬ [a, b, c] <+: [a, b, o2] :=
      higmanVCTauD2_inc_tail a (higmanVCTauD2_inc_tail b (higmanVCTauBridge_inc_cons [] [] ho2c))
    have tv : MapsCone (coneSwap [oa] [a, b, c] hT1 hT2) [a, b, o2] [a, b, o2] :=
      higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons [b, o2] [] hoa.symm) hi
    have e1 : m' = a :: b :: c :: k :: t := hm2 hvm
    have e2 : o' = [a, ob] ++ (a :: b :: o2 :: o4).drop [a, b, o2].length := ho1 hvo
    subst e1
    subst e2
    exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tu tv hu2 (by simp) tM
      (fixAB ((a :: b :: o2 :: o4).drop [a, b, o2].length))
      (by
        simp only [List.length_cons, List.length_append, List.length_drop,
          List.length_nil] <;> omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_classAB

end GroupApproximation.BooneHigman.Metabelian.Envelope
