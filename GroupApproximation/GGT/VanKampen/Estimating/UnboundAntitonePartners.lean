import Mathlib.Data.Nat.Find
import GroupApproximation.GGT.VanKampen.Estimating.UnboundMonotoneMorseIndex
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Antitone partners on a backwards pair, and the split point (route B1 of GapSpan)

Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*, arXiv:math/0411039v3,
Appendix, proof of Lemma 9.4; route B1 of `OsinLemma94ClassCaseGapSpanStatement` (ct-bilateral-cell, item 10).
A backwards connector pair `a < a'` on the source word and `b' < b` on the target word is split at breakpoints of
the source.

* `latestPartner near a' b g`: the largest target index `h ≤ b` that is a partner (`near g'' h`) of some source index
  `g'' ∈ [g, a']`.  It is antitone in `g` (`latestPartner_antitone`) for any relation `near`, and it is a partner of
  some later source point (`exists_later_partner`).
* `exists_step_lt_of_lt`, `exists_positive_split`: along any breakpoints `g₀ < … < g_m` an antitone partner function
  that decreases strictly overall decreases strictly at some step: the split point with a strictly positive target
  arc.
* Model tests: `antiparallelPartners` (source `sⁿ`, target `(s⁻¹)ⁿ`, partner `n - g`) is antitone with the right
  endpoints, the latest partner recovers it, and a breakpoint list of it has a strict step.
* **The metric half** (`exists_antitonePartners_of_morseRadius`, `exists_antitonePartners`).  Partners are target
  vertices within `P = B + 2κ + 6δ`; every source vertex has one (Morse proximity on both runs and
  `exists_close_of_endpoints_close` across the reversed target geodesic).  Let `L` be the latest partner of `g`,
  a partner of `g'' ≥ g`, and let `p ≤ L` be a partner of `g`.  With parameters `t, t''` on the source geodesic and
  `s_p, s_L` on the target geodesic, `index_lt_of_prefix_near` gives `t - t'' ≤ 3κ + 6δ` and `s_p - s_L ≤ 3κ + 6δ`.
  The corners pin `t + s` to within `B + 2κ + P` of the target length, so `t'' - t ≤ 4B + 11κ + 18δ` and
  `dist (g, L) ≤ 5B + 15κ + 24δ`.  In the Cayley realisation the constant is `δ + 6`.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open Classical in
/-- **The latest partner** of source index `g`: the largest `h ≤ b` partnered (`near g'' h`) with some source index
`g''` with `g ≤ g'' ≤ a'`, or `0` if there is none. -/
noncomputable def latestPartner (near : ℕ → ℕ → Prop) (a' b g : ℕ) : ℕ :=
  Nat.findGreatest (fun h => ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' h) b

theorem latestPartner_le (near : ℕ → ℕ → Prop) (a' b g : ℕ) : latestPartner near a' b g ≤ b := by
  classical
  exact Nat.findGreatest_le b

/-- **The latest partner is antitone** in the source index, for every partner relation. -/
theorem latestPartner_antitone (near : ℕ → ℕ → Prop) (a' b : ℕ) {g g' : ℕ} (hgg' : g ≤ g') :
    latestPartner near a' b g' ≤ latestPartner near a' b g := by
  classical
  unfold latestPartner
  exact Nat.findGreatest_mono
    (fun h ⟨g'', hg1, hg2, hnear⟩ => ⟨g'', le_trans hgg' hg1, hg2, hnear⟩) le_rfl

/-- A partner of `g` itself bounds the latest partner from below. -/
theorem le_latestPartner (near : ℕ → ℕ → Prop) {a' b g h : ℕ} (hga' : g ≤ a') (hhb : h ≤ b)
    (hnear : near g h) : h ≤ latestPartner near a' b g := by
  classical
  unfold latestPartner
  exact Nat.le_findGreatest hhb ⟨g, le_rfl, hga', hnear⟩

/-- **The latest partner is a partner of a later source point**, as soon as `g` has some partner `≤ b`. -/
theorem exists_later_partner (near : ℕ → ℕ → Prop) {a' b g h : ℕ} (hga' : g ≤ a') (hhb : h ≤ b)
    (hnear : near g h) :
    ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' (latestPartner near a' b g) := by
  classical
  unfold latestPartner
  exact Nat.findGreatest_spec (P := fun h => ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' h) hhb
    ⟨g, le_rfl, hga', hnear⟩

/-- **The split point.**  A function that decreases strictly from index `0` to index `m` decreases strictly at some
step `i < m`. -/
theorem exists_step_lt_of_lt (f : ℕ → ℕ) : ∀ m : ℕ, f m < f 0 → ∃ i < m, f (i + 1) < f i
  | 0, h => absurd h (lt_irrefl _)
  | m + 1, h => by
      by_cases hs : f (m + 1) < f m
      · exact ⟨m, Nat.lt_succ_self m, hs⟩
      · obtain ⟨i, hi, hfi⟩ := exists_step_lt_of_lt f m (lt_of_le_of_lt (not_lt.mp hs) h)
        exact ⟨i, Nat.lt_succ_of_lt hi, hfi⟩

/-- **The split point along breakpoints**: for breakpoints `gs 0, …, gs m` and a partner function `h` with
`h (gs m) < h (gs 0)`, some consecutive pair of breakpoints has a strictly positive target arc. -/
theorem exists_positive_split (h gs : ℕ → ℕ) (m : ℕ) (hback : h (gs m) < h (gs 0)) :
    ∃ i < m, h (gs (i + 1)) < h (gs i) :=
  exists_step_lt_of_lt (fun i => h (gs i)) m hback

/-! ## Model tests -/

/-- The antiparallel model: source `sⁿ`, target `(s⁻¹)ⁿ` read from `sⁿ`, so the source vertex `g` is the target
vertex `n - g`.  The partner function is `g ↦ n - g`. -/
def antiparallelPartners (n : ℕ) (g : ℕ) : ℕ := n - g

theorem antiparallelPartners_antitone (n : ℕ) {g g' : ℕ} (h : g ≤ g') :
    antiparallelPartners n g' ≤ antiparallelPartners n g := by
  unfold antiparallelPartners
  omega

theorem antiparallelPartners_endpoints (n : ℕ) :
    antiparallelPartners n 0 = n ∧ antiparallelPartners n n = 0 := by
  unfold antiparallelPartners
  omega

/-- In the antiparallel model, the latest partner for "same vertex" is the antiparallel partner. -/
theorem latestPartner_antiparallel (n g : ℕ) (hg : g ≤ n) :
    latestPartner (fun g'' h => g'' + h = n) n n g = antiparallelPartners n g := by
  refine le_antisymm ?_ (le_latestPartner (fun g'' h => g'' + h = n) hg
    (show antiparallelPartners n g ≤ n by unfold antiparallelPartners; omega)
    (show g + antiparallelPartners n g = n by unfold antiparallelPartners; omega))
  obtain ⟨g'', hg1, hg2, hnear⟩ := exists_later_partner (fun g'' h => g'' + h = n) (a' := n) (b := n)
    hg (Nat.sub_le n g) (show g + (n - g) = n by omega)
  have hnear' : g'' + latestPartner (fun g'' h => g'' + h = n) n n g = n := hnear
  unfold antiparallelPartners
  omega

/-- Closed calibration: along the breakpoints `0, 2, 5, 7` of the antiparallel model at `n = 7`, there is a step with
a strictly positive target arc. -/
theorem antiparallel_split_model :
    ∃ i < 3, antiparallelPartners 7 ([0, 2, 5, 7].getD (i + 1) 0) <
      antiparallelPartners 7 ([0, 2, 5, 7].getD i 0) :=
  ⟨0, by decide, by decide⟩

/-! ## The metric half -/

section Metric

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Reading a word from its vertex `a` visits the later vertices of the word. -/
theorem vertex_drop_run :
    ∀ (v : G) (word : List (RelLetter G Lambda)) (a k : ℕ),
      OsinComponents.vertex (OsinComponents.vertex v word a) (word.drop a) k =
        OsinComponents.vertex v word (a + k)
  | _, _, 0, _ => by simp only [OsinComponents.vertex_zero, List.drop_zero, Nat.zero_add]
  | _, [], _ + 1, _ => by simp only [OsinComponents.vertex_nil, List.drop_nil]
  | v, b :: t, a + 1, k => by
      rw [OsinComponents.vertex_cons_succ, List.drop_succ_cons,
        show a + 1 + k = a + k + 1 by omega, OsinComponents.vertex_cons_succ]
      exact vertex_drop_run (v * b.val) t a k

/-- **A run of a quasi-geodesic word and its geodesic.**  For vertices `a ≤ a'` of a `(λ, c)`-quasi-geodesic word
there is a geodesic from the vertex `a` to the vertex `a'` such that every vertex of the run is `κ`-close to it,
every point of it is `κ`-close to a vertex of the run, and the indices close to two of its points increase with the
parameter beyond the margin `3κ + 6δ`. -/
theorem exists_runGeodesic {D : RelGenSet G Lambda} {lambda c kappa δ : ℝ}
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa)
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {v : G} {S : ℕ → PointQuot D.alphabet}
    (hS : ∀ g, S g = vertexQuot D.alphabet (OsinComponents.vertex v word g))
    {a a' : ℕ} (haa' : a ≤ a') (ha' : a' ≤ word.length) :
    ∃ side : ℝ → PointQuot D.alphabet,
      IsGeodesicSegment side 0 (dist (S a) (S a')) ∧ side 0 = S a ∧
        side (dist (S a) (S a')) = S a' ∧
        (∀ g, a ≤ g → g ≤ a' →
          ∃ t ∈ Set.Icc (0 : ℝ) (dist (S a) (S a')), dist (side t) (S g) ≤ kappa) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (dist (S a) (S a')),
          ∃ g, a ≤ g ∧ g ≤ a' ∧ dist (side t) (S g) ≤ kappa) ∧
        (∀ g g', a ≤ g → g ≤ a' → a ≤ g' → g' ≤ a' →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (S a) (S a')), ∀ t' ∈ Set.Icc (0 : ℝ) (dist (S a) (S a')),
            dist (side t) (S g) ≤ kappa → dist (side t') (S g') ≤ kappa →
              t + (3 * kappa + 6 * δ) < t' → g < g') := by
  obtain ⟨sub, hsubdef⟩ : ∃ sub, sub = (word.drop a).take (a' - a) := ⟨_, rfl⟩
  have hsub : IsLambdaCQuasiGeodesicWord D lambda c sub := by
    rw [hsubdef]
    exact CutSections.isLambdaCQuasiGeodesicWord_drop_take hword a (a' - a)
  have hlen : sub.length = a' - a := by
    rw [hsubdef, List.length_take, List.length_drop]
    omega
  have hvert : ∀ k, k ≤ a' - a →
      vertexQuot D.alphabet (OsinComponents.vertex (OsinComponents.vertex v word a) sub k) =
        S (a + k) := by
    intro k hk
    rw [hS, hsubdef, vertex_take_prefix _ _ _ _ hk, vertex_drop_run]
  have hend : OsinComponents.vertex v word a * RelLetter.listVal sub =
      OsinComponents.vertex v word a' := by
    rw [← OsinComponents.vertex_length, hlen, hsubdef, vertex_take_prefix _ _ _ _ le_rfl,
      vertex_drop_run, Nat.add_sub_of_le haa']
  obtain ⟨side, hside, hside0, hside1⟩ := isGeodesicRealisationQuot D.alphabet (S a) (S a')
  have hmor := hmorse sub hsub (OsinComponents.vertex v word a) side
    (by rw [hend, ← hS, ← hS]; exact hside) (by rw [hside0, hS])
    (by rw [hend, ← hS, ← hS]; exact hside1)
  rw [hend, ← hS, ← hS] at hmor
  refine ⟨side, hside, hside0, hside1, ?_, ?_, ?_⟩
  · intro g hg hga'
    obtain ⟨t, ht, htd⟩ := hmor.1 (g - a) (by rw [hlen]; omega)
    refine ⟨t, ht, ?_⟩
    rw [dist_comm, ← Nat.add_sub_of_le hg, ← hvert (g - a) (by omega)]
    exact htd
  · intro t ht
    obtain ⟨i, hi, hid⟩ := hmor.2 t ht
    rw [hlen] at hi
    refine ⟨a + i, by omega, by omega, ?_⟩
    rw [← hvert i hi]
    exact hid
  · intro g g' hg hga' hg' hg'a' t ht t' ht' hnear hnear' hgap
    have hlt := index_lt_of_prefix_near (v := OsinComponents.vertex v word a) (a := g - a)
      (a' := g' - a) hδ hδ0 hmorse hsub hside (by rw [hside0, hS]) ht ht'
      (by rw [hlen]; omega)
      (by rw [hvert (g - a) (by omega), Nat.add_sub_of_le hg]; exact hnear)
      (by rw [hvert (g' - a) (by omega), Nat.add_sub_of_le hg']; exact hnear') hgap
    omega

/-- **Antitone partners across a backwards pair.**  Let `κ` be a Morse radius for `(λ, c)`-quasi-geodesic words in
a `δ`-hyperbolic realisation.  For source vertices `a < a'` and target vertices `b' ≤ b` whose corners are within
`B`, there is an antitone `h` from `[a, a']` to `[b', b]` with `h a = b`, `h a' = b'` and every connector within
`5 B + 15 κ + 24 δ`. -/
theorem exists_antitonePartners_of_morseRadius {D : RelGenSet G Lambda} {lambda c kappa δ : ℝ}
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa) (hkappa : 0 ≤ kappa) {B M : ℝ}
    (hM : 5 * B + 15 * kappa + 24 * δ ≤ M) {vs vt : G} {ws wt : List (RelLetter G Lambda)}
    (hws : IsLambdaCQuasiGeodesicWord D lambda c ws)
    (hwt : IsLambdaCQuasiGeodesicWord D lambda c wt) {a a' b b' : ℕ} (haa' : a < a')
    (ha' : a' ≤ ws.length) (hbb' : b' ≤ b) (hb : b ≤ wt.length)
    (hstart : dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws a))
      (vertexQuot D.alphabet (OsinComponents.vertex vt wt b)) ≤ B)
    (hend : dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws a'))
      (vertexQuot D.alphabet (OsinComponents.vertex vt wt b')) ≤ B) :
    ∃ h : ℕ → ℕ, h a = b ∧ h a' = b' ∧
      (∀ g g', a ≤ g → g ≤ g' → g' ≤ a' → h g' ≤ h g) ∧
      ∀ g, a ≤ g → g ≤ a' → b' ≤ h g ∧ h g ≤ b ∧
        dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws g))
          (vertexQuot D.alphabet (OsinComponents.vertex vt wt (h g))) ≤ M := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ → PointQuot D.alphabet,
      ∀ g, S g = vertexQuot D.alphabet (OsinComponents.vertex vs ws g) := ⟨_, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → PointQuot D.alphabet,
      ∀ p, T p = vertexQuot D.alphabet (OsinComponents.vertex vt wt p) := ⟨_, fun _ => rfl⟩
  rw [← hS, ← hT] at hstart hend
  have hB0 : 0 ≤ B := le_trans dist_nonneg hstart
  obtain ⟨σ, hσ, hσ0, hσ1, hSσ, -, hSmono⟩ := exists_runGeodesic hδ hδ0 hmorse hws hS haa'.le ha'
  obtain ⟨τ, hτ, hτ0, hτ1, hTτ, hτT, hTmono⟩ := exists_runGeodesic hδ hδ0 hmorse hwt hT hbb' hb
  obtain ⟨near, hnear⟩ : ∃ near : ℕ → ℕ → Prop,
      ∀ g p, near g p ↔ dist (S g) (T p) ≤ B + 2 * kappa + 6 * δ := ⟨_, fun _ _ => Iff.rfl⟩
  -- every source vertex of the run has a partner on the target run
  have hpartner : ∀ g, a ≤ g → g ≤ a' → ∃ p, b' ≤ p ∧ p ≤ b ∧ near g p := by
    intro g hg hga'
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
    refine ⟨p, hp1, hp2, (hnear g p).mpr ?_⟩
    have h4 := dist_triangle4 (S g) (σ t) (τ (dist (T b') (T b) - s)) (T p)
    rw [dist_comm (S g) (σ t)] at h4
    linarith
  have hb'L : ∀ g, g ≤ a' → b' ≤ latestPartner near a' b g := fun g hg =>
    le_trans (le_latestPartner near (a' := a') (b := b) (g := a') (h := b') le_rfl hbb'
      ((hnear a' b').mpr (by linarith))) (latestPartner_antitone near a' b hg)
  refine ⟨fun g => if a' ≤ g then b' else latestPartner near a' b g, ?_, ?_, ?_, ?_⟩
  · show (if a' ≤ a then b' else latestPartner near a' b a) = b
    rw [if_neg (show ¬ a' ≤ a by omega)]
    exact le_antisymm (latestPartner_le near a' b a)
      (le_latestPartner near (a' := a') (b := b) (g := a) (h := b) haa'.le le_rfl
        ((hnear a b).mpr (by linarith)))
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
  · intro g hg hga'
    show b' ≤ (if a' ≤ g then b' else latestPartner near a' b g) ∧
      (if a' ≤ g then b' else latestPartner near a' b g) ≤ b ∧
      dist (vertexQuot D.alphabet (OsinComponents.vertex vs ws g))
        (vertexQuot D.alphabet
          (OsinComponents.vertex vt wt (if a' ≤ g then b' else latestPartner near a' b g))) ≤ M
    rw [← hS, ← hT]
    by_cases h1 : a' ≤ g
    · have hga : g = a' := le_antisymm hga' h1
      rw [if_pos h1, hga]
      exact ⟨le_rfl, hbb', by linarith⟩
    · rw [if_neg h1]
      refine ⟨hb'L g hga', latestPartner_le near a' b g, ?_⟩
      obtain ⟨p, hp1, hp2, hpnear⟩ := hpartner g hg hga'
      have hpL := le_latestPartner near hga' hp2 hpnear
      obtain ⟨g'', hg1, hg2, hg''near⟩ := exists_later_partner near hga' hp2 hpnear
      have hb'L' := hb'L g hga'
      have hLb := latestPartner_le near a' b g
      set L := latestPartner near a' b g with hLdef
      have hd1 := (hnear g p).mp hpnear
      have hd2 := (hnear g'' L).mp hg''near
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
      have hlow : dist (T b) (τ sp) ≤ B + t + 2 * kappa + (B + 2 * kappa + 6 * δ) := by
        have e1 := dist_triangle4 (T b) (S a) (σ t) (S g)
        have e2 := dist_triangle4 (T b) (S g) (T p) (τ sp)
        rw [dist_comm (T b) (S a), hσt] at e1
        rw [dist_comm (T p) (τ sp)] at e2
        linarith
      have hhigh : dist (S a) (σ t'') ≤
          B + dist (T b) (τ sL) + 2 * kappa + (B + 2 * kappa + 6 * δ) := by
        have e1 := dist_triangle4 (S a) (T b) (τ sL) (T L)
        have e2 := dist_triangle4 (S a) (T L) (S g'') (σ t'')
        rw [dist_comm (T L) (S g''), dist_comm (S g'') (σ t'')] at e2
        linarith
      have hback : t'' - t ≤ 4 * B + 11 * kappa + 18 * δ := by
        rw [hτs sp hsp] at hlow
        rw [hσt'', hτs sL hsL] at hhigh
        linarith
      have hσσ : dist (σ t) (σ t'') ≤ 4 * B + 11 * kappa + 18 * δ := by
        rw [hσ t ht t'' ht'']
        exact abs_sub_le_iff.mpr ⟨by linarith, hback⟩
      have e1 := dist_triangle4 (S g) (σ t) (σ t'') (S g'')
      have e2 := dist_triangle (S g) (S g'') (T L)
      rw [dist_comm (S g) (σ t)] at e1
      linarith

/-- **Antitone partners** (route B1 of GapSpan) for `(λ, c + 2)`-quasi-geodesic words over a `δ`-hyperbolic Cayley
graph: one radius `κ`, margin `5 B + 15 κ + 24 (δ + 6)`, connectors measured by `wordDist`. -/
theorem exists_antitonePartners (D : RelGenSet G Lambda) (lambda c : ℝ) (hlambda : 0 < lambda) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet)) (hδ0 : 0 ≤ δ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∀ B M : ℝ, 5 * B + 15 * kappa + 24 * (δ + 6) ≤ M →
      ∀ (vs vt : G) (ws wt : List (RelLetter G Lambda)),
        IsLambdaCQuasiGeodesicWord D lambda (c + 2) ws →
        IsLambdaCQuasiGeodesicWord D lambda (c + 2) wt →
        ∀ {a a' b b' : ℕ}, a < a' → a' ≤ ws.length → b' ≤ b → b ≤ wt.length →
          (wordDist D.alphabet.carrier (OsinComponents.vertex vs ws a)
            (OsinComponents.vertex vt wt b) : ℝ) ≤ B →
          (wordDist D.alphabet.carrier (OsinComponents.vertex vs ws a')
            (OsinComponents.vertex vt wt b') : ℝ) ≤ B →
          ∃ h : ℕ → ℕ, h a = b ∧ h a' = b' ∧
            (∀ g g', a ≤ g → g ≤ g' → g' ≤ a' → h g' ≤ h g) ∧
            ∀ g, a ≤ g → g ≤ a' → b' ≤ h g ∧ h g ≤ b ∧
              (wordDist D.alphabet.carrier (OsinComponents.vertex vs ws g)
                (OsinComponents.vertex vt wt (h g)) : ℝ) ≤ M := by
  obtain ⟨kappa, hkappa, hmorse⟩ := exists_word_replacement_morse D lambda (c + 2) hlambda hδ hδ0
  refine ⟨kappa, hkappa, ?_⟩
  intro B M hM vs vt ws wt hws hwt a a' b b' haa' ha' hbb' hb hstart hend
  obtain ⟨h, hha, hha', hanti, hbound⟩ := exists_antitonePartners_of_morseRadius
    (lambda := lambda) (c := c + 2)
    (isHyperbolicSpace_pointQuot (isHyperbolicSpace_point D.alphabet hδ)) (by linarith) hmorse
    hkappa hM hws hwt haa' ha' hbb' hb (by rw [dist_vertexQuot]; exact hstart)
    (by rw [dist_vertexQuot]; exact hend)
  refine ⟨h, hha, hha', hanti, fun g hg hga' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hbound g hg hga'
  rw [dist_vertexQuot] at h3
  exact ⟨h1, h2, h3⟩

end Metric

end GroupApproximation.GGT.VanKampen.UnboundEstimate

/-! ### Audit -/

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.latestPartner_antitone
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.le_latestPartner
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_later_partner
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_step_lt_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_positive_split
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.latestPartner_antiparallel
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.antiparallel_split_model
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.vertex_drop_run
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_runGeodesic
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_antitonePartners_of_morseRadius
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_antitonePartners
