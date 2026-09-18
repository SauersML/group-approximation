import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Words
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-letter residual: other word starting with the other letter (lane bh-met-77v)

Main word `m = a b c k t`, other word `o = o₀ o''` with `o₀ ≠ a`, two letters.  The root is
`T = ([a, b̄], [a, b, c])` (`b̄` the other letter); it carries `m ↦ a b̄ k t` and fixes `o`.
The shorter word `u` of the level-lowering swap is `[a, b̄]` or `[o₀, u₁]`, and `|v| = 3`.
Either `(u, v)` is the root, or `T` gives a direct edge into `(u, v)`
(`higmanVCTauD2_classOB`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The shape of `u` when `o₀ ≠ a`. -/
theorem higmanVCTauD2_ob_u {d : ℕ} {a b c k ob o0 : Fin d} {t o'' u v : List (Fin d)}
    (hbina : ∀ e : Fin d, e ≠ a → e = o0) (hbinb : ∀ e : Fin d, e ≠ b → e = ob)
    (hv3 : v.length ≤ 3) (hlt : u.length < v.length)
    (hum : ¬ u <+: a :: b :: c :: k :: t) (huo : ¬ u <+: o0 :: o'') :
    u = [a, ob] ∨ ∃ u1, u = [o0, u1] := by
  rcases u with _ | ⟨u0, _ | ⟨u1, _ | ⟨u3, u4⟩⟩⟩
  · exact (hum List.nil_prefix).elim
  · by_cases h0 : u0 = a
    · refine (hum ?_).elim
      rw [h0]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
    · refine (huo ?_).elim
      rw [hbina u0 h0]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
  · by_cases h0 : u0 = a
    · by_cases h1 : u1 = b
      · refine (hum ?_).elim
        rw [h0, h1]
        exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
      · left
        rw [h0, hbinb u1 h1]
    · right
      exact ⟨u1, by rw [hbina u0 h0]⟩
  · simp only [List.length_cons] at hlt <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_ob_u

/-- **Class `o₀ ≠ a`.**  The level-lowering swap is the root or has a direct edge from it. -/
theorem higmanVCTauD2_classOB {d : ℕ} {a b c k ob o0 : Fin d} {t o'' u v m' o' : List (Fin d)}
    (hob : ob ≠ b) (ho0 : o0 ≠ a) (hbina : ∀ e : Fin d, e ≠ a → e = o0)
    (hbinb : ∀ e : Fin d, e ≠ b → e = ob)
    (hUV : higmanVCTauD2_UV d u v (a :: b :: c :: k :: t) (o0 :: o'') m' o') :
    higmanVCTauD2_Good d [a, ob] [a, b, c] (a :: b :: c :: k :: t) (o0 :: o'') u v m' o' := by
  obtain ⟨hv3, hlt, hum, huo, hvmo, hm1, hm2, ho1, ho2⟩ := hUV
  obtain ⟨hT1, hT2⟩ : ¬ [a, ob] <+: [a, b, c] ∧ ¬ [a, b, c] <+: [a, ob] :=
    higmanVCTauBridge_inc_pair [c] hob
  have fixO : ∀ (e : Fin d) (r : List (Fin d)), e ≠ a →
      MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) (e :: r) (e :: r) := fun e r he =>
    higmanVCTauD2_fix hT1 hT2 (higmanVCTauBridge_inc_cons r [ob] he)
      (higmanVCTauBridge_inc_cons r [b, c] he)
  have tP : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) [a, ob] [a, b, c] :=
    mapsCone_coneSwap_left hT1 hT2
  have tQ : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) [a, b, c] [a, ob] :=
    mapsCone_coneSwap_right hT1 hT2
  have tM : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) (a :: b :: c :: k :: t)
      (a :: ob :: k :: t) := tQ.append (k :: t)
  have tO := fixO o0 o'' ho0
  have ht : (a :: ob :: k :: t).length + (o0 :: o'').length <
      (a :: b :: c :: k :: t).length + (o0 :: o'').length := by
    simp only [List.length_cons] <;> omega
  have hu := higmanVCTauD2_ob_u hbina hbinb hv3 hlt hum huo
  have hP : [a, ob].length ≤ 3 := by simp
  have hQ : [a, b, c].length ≤ 3 := by simp
  rcases hu with rfl | ⟨u1, rfl⟩
  · have hv : v.length = 3 := by
      simp only [List.length_cons, List.length_nil] at hlt
      omega
    by_cases hvm : v <+: a :: b :: c :: k :: t
    · obtain rfl := higmanVCTauD2_pre3 hvm hv
      unfold higmanVCTauD2_Good
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · have hvo : v <+: o0 :: o'' := hvmo.resolve_left hvm
      have hvl : v.length ≤ o''.length + 1 := hvo.length_le
      obtain ⟨v', hv', -⟩ := higmanVCTauD2_pre1 hvo (by omega)
      have tv : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) v v := by
        rw [hv']
        exact fixO o0 v' ho0
      have e1 : m' = a :: b :: c :: k :: t := hm2 hvm
      have e2 : o' = [a, ob] ++ (o0 :: o'').drop v.length := ho1 hvo
      subst e1
      subst e2
      exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tP tv hQ hv3 tM
        (tP.append _) (by
          simp only [List.length_cons, List.length_append, List.length_drop,
            List.length_nil] <;> omega)
  · have hv : v.length = 3 := by
      simp only [List.length_cons, List.length_nil] at hlt
      omega
    have tu : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) [o0, u1] [o0, u1] :=
      fixO o0 [u1] ho0
    have hu2 : [o0, u1].length ≤ 3 := by simp
    by_cases hvm : v <+: a :: b :: c :: k :: t
    · obtain rfl := higmanVCTauD2_pre3 hvm hv
      have hvo : ¬ [a, b, c] <+: o0 :: o'' := (higmanVCTauBridge_inc_cons o'' [b, c] ho0).2
      have e1 : m' = o0 :: u1 :: k :: t := hm1 hvm
      have e2 : o' = o0 :: o'' := ho2 hvo
      subst e1
      subst e2
      exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tu tQ hu2 hP
        (fixO o0 (u1 :: k :: t) ho0) tO (by simp only [List.length_cons] <;> omega)
    · have hvo : v <+: o0 :: o'' := hvmo.resolve_left hvm
      have hvl : v.length ≤ o''.length + 1 := hvo.length_le
      obtain ⟨v', hv', -⟩ := higmanVCTauD2_pre1 hvo (by omega)
      have tv : MapsCone (coneSwap [a, ob] [a, b, c] hT1 hT2) v v := by
        rw [hv']
        exact fixO o0 v' ho0
      have e1 : m' = a :: b :: c :: k :: t := hm2 hvm
      have e2 : o' = [o0, u1] ++ (o0 :: o'').drop v.length := ho1 hvo
      subst e1
      subst e2
      exact higmanVCTauD2_mkDirect hT1 hT2 hP hQ tM tO ht tu tv hu2 hv3 tM
        (fixO o0 (u1 :: (o0 :: o'').drop v.length) ho0) (by
          simp only [List.length_cons, List.length_append, List.length_drop,
            List.length_nil] <;> omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_classOB

end GroupApproximation.BooneHigman.Metabelian.Envelope
