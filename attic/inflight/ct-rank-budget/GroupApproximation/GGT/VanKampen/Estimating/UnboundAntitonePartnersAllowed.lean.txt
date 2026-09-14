import GroupApproximation.GGT.VanKampen.Estimating.UnboundAntitonePartners
import GroupApproximation.Meta.AxiomGuard

/-!
# Antitone partners at allowed positions (route B1 of GapSpan, on class words)

Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*, arXiv:math/0411039v3,
Appendix, proof of Lemma 9.4.  On class words the vertices strictly inside a gap are no side vertices, and a gap does not
move a vertex.  The partner selection of `exists_antitonePartners_of_morseRadius` is refined:

* partners are taken only between allowed source positions and allowed target positions;
* every target position lies within `Γ` of an allowed one of the target run, at the cost `3 Γ` in the margin;
* across a run of disallowed source positions between two allowed positions with one vertex, the partner does not
  change.  The latest partner of the first is witnessed at an allowed later position, which is the first itself or
  lies beyond the run.

* `le_latestPartner_of_later`: a partner of a later source point bounds the latest partner.
* `exists_antitonePartners_allowed_of_morseRadius`: margin `5 B + 15 κ + 24 δ + 3 Γ`.

Model test: with every position allowed and `Γ = 0`, the conclusions are those of
`exists_antitonePartners_of_morseRadius` (margin `5 B + 15 κ + 24 δ`), and the gap clause is vacuous.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- A partner of a later source point bounds the latest partner from below. -/
theorem le_latestPartner_of_later (near : ℕ → ℕ → Prop) {a' b g g'' h : ℕ} (hg : g ≤ g'')
    (hg'' : g'' ≤ a') (hhb : h ≤ b) (hnear : near g'' h) : h ≤ latestPartner near a' b g := by
  classical
  unfold latestPartner
  exact Nat.le_findGreatest hhb ⟨g'', hg, hg'', hnear⟩

section Metric

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Antitone partners at allowed positions.**  As `exists_antitonePartners_of_morseRadius`, with partners between
allowed positions, target positions within `Γ` of allowed ones, margin `5 B + 15 κ + 24 δ + 3 Γ`, and one partner
across a run of disallowed source positions between two allowed positions with one vertex. -/
theorem exists_antitonePartners_allowed_of_morseRadius {D : RelGenSet G Lambda} {lambda c kappa δ : ℝ}
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa) (hkappa : 0 ≤ kappa) {B Γ M : ℝ}
    (hM : 5 * B + 15 * kappa + 24 * δ + 3 * Γ ≤ M) {vs vt : G} {ws wt : List (RelLetter G Lambda)}
    (hws : IsLambdaCQuasiGeodesicWord D lambda c ws)
    (hwt : IsLambdaCQuasiGeodesicWord D lambda c wt) (allowS allowT : ℕ → Prop) {a a' b b' : ℕ}
    (haa' : a < a') (ha' : a' ≤ ws.length) (hbb' : b' ≤ b) (hb : b ≤ wt.length)
    (haS : allowS a) (ha'S : allowS a') (hbT : allowT b) (hb'T : allowT b')
    (hΓ : ∀ p, b' ≤ p → p ≤ b → ∃ p', b' ≤ p' ∧ p' ≤ b ∧ allowT p' ∧
      dist (vertexQuot D.alphabet (OsinComponents.vertex vt wt p))
        (vertexQuot D.alphabet (OsinComponents.vertex vt wt p')) ≤ Γ)
    (hstart : dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws a))
      (vertexQuot D.alphabet (OsinComponents.vertex vt wt b)) ≤ B)
    (hend : dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws a'))
      (vertexQuot D.alphabet (OsinComponents.vertex vt wt b')) ≤ B) :
    ∃ h : ℕ → ℕ, h a = b ∧ h a' = b' ∧
      (∀ g g', a ≤ g → g ≤ g' → g' ≤ a' → h g' ≤ h g) ∧
      (∀ g, a ≤ g → g ≤ a' → allowS g → b' ≤ h g ∧ h g ≤ b ∧ allowT (h g) ∧
        dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws g))
          (vertexQuot D.alphabet (OsinComponents.vertex vt wt (h g))) ≤ M) ∧
      (∀ g, a ≤ g → g < a' → allowS g → ∀ q, q ≤ b → allowT q →
        OsinComponents.vertex vt wt q = OsinComponents.vertex vt wt (h g) → q ≤ h g) ∧
      (∀ g g', a ≤ g → g < g' → g' < a' → allowS g → allowS g' →
        (∀ x, g < x → x < g' → ¬ allowS x) →
        OsinComponents.vertex vs ws g = OsinComponents.vertex vs ws g' → h g = h g') := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ → PointQuot D.alphabet,
      ∀ g, S g = vertexQuot D.alphabet (OsinComponents.vertex vs ws g) := ⟨_, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → PointQuot D.alphabet,
      ∀ p, T p = vertexQuot D.alphabet (OsinComponents.vertex vt wt p) := ⟨_, fun _ => rfl⟩
  rw [← hS, ← hT] at hstart hend
  have hB0 : 0 ≤ B := le_trans dist_nonneg hstart
  have hΓ0 : 0 ≤ Γ := by
    obtain ⟨p', -, -, -, hd⟩ := hΓ b' le_rfl hbb'
    exact le_trans dist_nonneg hd
  obtain ⟨σ, hσ, hσ0, hσ1, hSσ, -, hSmono⟩ := exists_runGeodesic hδ hδ0 hmorse hws hS haa'.le ha'
  obtain ⟨τ, hτ, hτ0, hτ1, hTτ, hτT, hTmono⟩ := exists_runGeodesic hδ hδ0 hmorse hwt hT hbb' hb
  obtain ⟨near, hnear⟩ : ∃ near : ℕ → ℕ → Prop,
      ∀ g p, near g p ↔ allowS g ∧ allowT p ∧ dist (S g) (T p) ≤ B + 2 * kappa + 6 * δ + Γ :=
    ⟨_, fun _ _ => Iff.rfl⟩
  -- every allowed source vertex of the run has an allowed partner on the target run
  have hpartner : ∀ g, a ≤ g → g ≤ a' → allowS g → ∃ p, b' ≤ p ∧ p ≤ b ∧ near g p := by
    intro g hg hga' hgS
    obtain ⟨t, ht, htd⟩ := hSσ g hg hga'
    have hLL : dist (T b') (T b) - 0 = dist (T b) (T b') := by rw [sub_zero, dist_comm]
    have hτr : IsGeodesicSegment (fun r => τ (dist (T b') (T b) - r)) 0 (dist (T b) (T b')) := by
      have h0 := Olshanskii.isGeodesicSegment_shift_rev (u := 0) (u' := dist (T b') (T b)) hτ
        le_rfl le_rfl
      rwa [hLL] at h0
    obtain ⟨s, hs, hsd⟩ := Olshanskii.exists_close_of_endpoints_close hδ hδ0
      (isGeodesicRealisationQuot D.alphabet) hσ hσ0 hσ1 hτr
      (show τ (dist (T b') (T b) - 0) = T b by rw [sub_zero]; exact hτ1)
      (show τ (dist (T b') (T b) - dist (T b) (T b')) = T b' by
        rw [dist_comm (T b) (T b'), sub_self]; exact hτ0)
      hstart hend ht
    have hsd' : dist (σ t) (τ (dist (T b') (T b) - s)) ≤ B + 6 * δ := hsd
    have hs' : dist (T b') (T b) - s ∈ Set.Icc (0 : ℝ) (dist (T b') (T b)) := by
      have h1 := hs.1
      have h2 := hs.2
      rw [dist_comm (T b) (T b')] at h2
      exact ⟨by linarith, by linarith⟩
    obtain ⟨p, hp1, hp2, hpd⟩ := hτT _ hs'
    have hd : dist (S g) (T p) ≤ B + 2 * kappa + 6 * δ := by
      have h4 := dist_triangle4 (S g) (σ t) (τ (dist (T b') (T b) - s)) (T p)
      rw [dist_comm (S g) (σ t)] at h4
      linarith
    obtain ⟨p', hp'1, hp'2, hp'T, hp'd⟩ := hΓ p hp1 hp2
    rw [← hT, ← hT] at hp'd
    refine ⟨p', hp'1, hp'2, (hnear g p').mpr ⟨hgS, hp'T, ?_⟩⟩
    have h3 := dist_triangle (S g) (T p) (T p')
    linarith
  have hb'L : ∀ g, g ≤ a' → b' ≤ latestPartner near a' b g := fun g hg =>
    le_trans (le_latestPartner near (a' := a') (b := b) (g := a') (h := b') le_rfl hbb'
      ((hnear a' b').mpr ⟨ha'S, hb'T, by linarith⟩)) (latestPartner_antitone near a' b hg)
  refine ⟨fun g => if a' ≤ g then b' else latestPartner near a' b g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (if a' ≤ a then b' else latestPartner near a' b a) = b
    rw [if_neg (show ¬ a' ≤ a by omega)]
    exact le_antisymm (latestPartner_le near a' b a)
      (le_latestPartner near (a' := a') (b := b) (g := a) (h := b) haa'.le le_rfl
        ((hnear a b).mpr ⟨haS, hbT, by linarith⟩))
  · show (if a' ≤ a' then b' else latestPartner near a' b a') = b'
    rw [if_pos (le_refl a')]
  · intro g g' hg hgg' hg'a'
    show (if a' ≤ g' then b' else latestPartner near a' b g') ≤
      (if a' ≤ g then b' else latestPartner near a' b g)
    by_cases h1 : a' ≤ g
    · simp only [if_pos (le_trans h1 hgg'), if_pos h1, le_refl]
    · rw [if_neg h1]
      by_cases h2 : a' ≤ g'
      · rw [if_pos h2]
        exact hb'L g (by omega)
      · rw [if_neg h2]
        exact latestPartner_antitone near a' b hgg'
  · intro g hg hga' hgS
    show b' ≤ (if a' ≤ g then b' else latestPartner near a' b g) ∧
      (if a' ≤ g then b' else latestPartner near a' b g) ≤ b ∧
      allowT (if a' ≤ g then b' else latestPartner near a' b g) ∧
      dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws g))
        (vertexQuot D.alphabet
          (OsinComponents.vertex vt wt (if a' ≤ g then b' else latestPartner near a' b g))) ≤ M
    rw [← hS, ← hT]
    by_cases h1 : a' ≤ g
    · have hga : g = a' := le_antisymm hga' h1
      rw [if_pos h1, hga]
      exact ⟨le_rfl, hbb', hb'T, by linarith⟩
    · rw [if_neg h1]
      obtain ⟨p, hp1, hp2, hpnear⟩ := hpartner g hg hga' hgS
      have hpL := le_latestPartner near hga' hp2 hpnear
      obtain ⟨g'', hg1, hg2, hg''near⟩ := exists_later_partner near hga' hp2 hpnear
      have hb'L' := hb'L g hga'
      have hLb := latestPartner_le near a' b g
      set L := latestPartner near a' b g with hLdef
      obtain ⟨-, -, hd1⟩ := (hnear g p).mp hpnear
      obtain ⟨-, hLT, hd2⟩ := (hnear g'' L).mp hg''near
      refine ⟨hb'L', hLb, hLT, ?_⟩
      obtain ⟨t, ht, htd⟩ := hSσ g hg hga'
      obtain ⟨t'', ht'', ht''d⟩ := hSσ g'' (le_trans hg hg1) hg2
      obtain ⟨sp, hsp, hspd⟩ := hTτ p hp1 hp2
      obtain ⟨sL, hsL, hsLd⟩ := hTτ L hb'L' hLb
      -- the orientation on each run
      have hsrc : t - t'' ≤ 3 * kappa + 6 * δ := by
        by_contra hcon
        have hlt := hSmono g'' g (le_trans hg hg1) hg2 hg hga' t'' ht'' t ht ht''d htd
          (by linarith)
        omega
      have htgt : sp - sL ≤ 3 * kappa + 6 * δ := by
        by_contra hcon
        have hlt := hTmono L p hb'L' hLb hp1 hp2 sL hsL sp hsp hsLd hspd (by linarith)
        omega
      -- parameters are distances from the corners
      have hσt : dist (S a) (σ t) = t := by
        have h0 := hσ 0 ⟨le_rfl, dist_nonneg⟩ t ht
        rw [hσ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at h0
        exact h0
      have hσt'' : dist (S a) (σ t'') = t'' := by
        have h0 := hσ 0 ⟨le_rfl, dist_nonneg⟩ t'' ht''
        rw [hσ0, zero_sub, abs_neg, abs_of_nonneg ht''.1] at h0
        exact h0
      have hτs : ∀ s ∈ Set.Icc (0 : ℝ) (dist (T b') (T b)),
          dist (T b) (τ s) = dist (T b') (T b) - s := by
        intro s hs
        have h0 := hτ (dist (T b') (T b)) ⟨dist_nonneg, le_rfl⟩ s hs
        rw [hτ1, abs_of_nonneg (show (0 : ℝ) ≤ dist (T b') (T b) - s by linarith [hs.2])] at h0
        exact h0
      -- the corners pin `t + s` near the target length
      have hlow : dist (T b) (τ sp) ≤ B + t + 2 * kappa + (B + 2 * kappa + 6 * δ + Γ) := by
        have e1 := dist_triangle4 (T b) (S a) (σ t) (S g)
        have e2 := dist_triangle4 (T b) (S g) (T p) (τ sp)
        rw [dist_comm (T b) (S a), hσt] at e1
        rw [dist_comm (T p) (τ sp)] at e2
        linarith
      have hhigh : dist (S a) (σ t'') ≤
          B + dist (T b) (τ sL) + 2 * kappa + (B + 2 * kappa + 6 * δ + Γ) := by
        have e1 := dist_triangle4 (S a) (T b) (τ sL) (T L)
        have e2 := dist_triangle4 (S a) (T L) (S g'') (σ t'')
        rw [dist_comm (T L) (S g''), dist_comm (S g'') (σ t'')] at e2
        linarith
      have hback : t'' - t ≤ 4 * B + 11 * kappa + 18 * δ + 2 * Γ := by
        rw [hτs sp hsp] at hlow
        rw [hσt'', hτs sL hsL] at hhigh
        linarith
      have hσσ : dist (σ t) (σ t'') ≤ 4 * B + 11 * kappa + 18 * δ + 2 * Γ := by
        rw [hσ t ht t'' ht'']
        exact abs_sub_le_iff.mpr ⟨by linarith, hback⟩
      have e1 := dist_triangle4 (S g) (σ t) (σ t'') (S g'')
      have e2 := dist_triangle (S g) (S g'') (T L)
      rw [dist_comm (S g) (σ t)] at e1
      linarith
  · intro g hg hga' hgS q hqb hqT hqeq
    have hng : ¬ a' ≤ g := by omega
    beta_reduce at hqeq ⊢
    rw [if_neg hng] at hqeq ⊢
    obtain ⟨p, hp1, hp2, hpnear⟩ := hpartner g hg hga'.le hgS
    obtain ⟨g'', hg1, hg2, hg''near⟩ := exists_later_partner near hga'.le hp2 hpnear
    obtain ⟨hg''S, -, hd⟩ := (hnear g'' _).mp hg''near
    have hTq : T q = T (latestPartner near a' b g) := by rw [hT, hT, hqeq]
    rw [← hTq] at hd
    exact le_latestPartner_of_later near hg1 hg2 hqb ((hnear g'' q).mpr ⟨hg''S, hqT, hd⟩)
  · intro g g' hg hgg' hg'a' hgS hg'S hbetween hSeq
    show (if a' ≤ g then b' else latestPartner near a' b g) =
      (if a' ≤ g' then b' else latestPartner near a' b g')
    rw [if_neg (show ¬ a' ≤ g by omega), if_neg (show ¬ a' ≤ g' by omega)]
    refine le_antisymm ?_ (latestPartner_antitone near a' b hgg'.le)
    obtain ⟨p, hp1, hp2, hpnear⟩ := hpartner g hg (by omega) hgS
    obtain ⟨g'', hg1, hg2, hg''near⟩ := exists_later_partner near (show g ≤ a' by omega) hp2 hpnear
    have hLb := latestPartner_le near a' b g
    by_cases hlt : g' ≤ g''
    · exact le_latestPartner_of_later near hlt hg2 hLb hg''near
    · obtain ⟨hg''S, hLT, hd⟩ := (hnear g'' _).mp hg''near
      have hgg'' : g'' = g := by
        by_contra hne
        exact hbetween g'' (by omega) (by omega) hg''S
      rw [hgg''] at hd
      have hSgg : S g = S g' := by rw [hS, hS, hSeq]
      rw [hSgg] at hd
      exact le_latestPartner near (show g' ≤ a' by omega) hLb ((hnear g' _).mpr ⟨hg'S, hLT, hd⟩)

end Metric

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.le_latestPartner_of_later
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_antitonePartners_allowed_of_morseRadius
