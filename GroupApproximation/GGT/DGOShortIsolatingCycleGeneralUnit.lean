import GroupApproximation.GGT.DGOQuasiGeodesicFourGonNormalise

/-!
# Short isolating cycles at general parameters: the unit component case

Choose a scaled corner offset `A` using the uniform thinness radius. Every
vertex retained by a splice lies in a fixed ball about the basepoint. On each
quasi-geodesic side, two such vertices have uniformly bounded index distance.
This controls every branch with one bound, while the connectors avoid the
distinguished coset by the metric offset.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The general-parameter short-cycle construction with a one-letter exempt
component. The length bound is chosen before all polygons. -/
theorem exists_short_isolating_cycleAt_of_unit
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (mu : ℝ) (b δ : ℕ) (hmu : 0 < mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ L : ℕ, ∀ (lam : Lambda) (v : G) (w : List (RelLetter G Lambda)) (c : ℕ → ℕ),
      QuasiGeodesicFourGon D mu b v w c → c 1 = 1 →
      IsComp lam w 0 1 → IsIsolated D.fam lam v w 0 →
      ∃ q : List (RelLetter G Lambda),
        (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
        q.length ≤ L ∧ IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
        (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  obtain ⟨θ, hθ⟩ := exists_quasiGeodesicFourGon_thinness D mu b δ hmu hδ
  let A := ⌈mu⌉₊ * (θ + b + 3)
  let T := A + θ + 2
  let Q := ⌈mu⌉₊ * (2 * T + b)
  let L := 2 * A + 2 * θ + 2 * Q + 10
  refine ⟨L, ?_⟩
  intro lam v w c hQ hc1 hcomp hiso
  obtain ⟨hthin1, hthin3⟩ := hθ v w c hQ
  have hS := D.alphabet.symmetricGenerating
  have hfin : c 4 = w.length := hQ.finish
  have h12 : c 1 ≤ c 2 := hQ.mono (by omega : 1 ≤ 2)
  have h23 : c 2 ≤ c 3 := hQ.mono (by omega : 2 ≤ 3)
  have h34 : c 3 ≤ c 4 := hQ.mono (by omega : 3 ≤ 4)
  have hlast : vertex v w (c 4) = v := by
    rw [hfin, vertex_eq_mul_listVal_take, List.take_length, hQ.closed, mul_one]
  have hd01 : wordDist D.alphabet.carrier v (vertex v w (c 1)) ≤ 1 := by
    have h := wordDist_le_one_of_mem_fam D (span_mem_fam_of_isComp D v hQ.letters hcomp)
    simpa only [vertex_zero, hc1] using h
  have hd04 : wordDist D.alphabet.carrier v (vertex v w (c 4)) = 0 := by
    simp only [hlast, wordDist_self]
  have hfirst_upper : ∀ p : ℕ, c 1 ≤ p → p ≤ c 2 →
      wordDist D.alphabet.carrier v (vertex v w p) ≤ p := by
    intro p hp hp2
    have h := (hQ.side_dist_of_mem D (s := 1) (by omega) (by omega) le_rfl hp hp2).2
    have htri := wordDist_triangle hS v (vertex v w (c 1)) (vertex v w p)
    omega
  have hthird_upper : ∀ p : ℕ, c 3 ≤ p → p ≤ c 4 →
      wordDist D.alphabet.carrier v (vertex v w p) ≤ w.length - p := by
    intro p hp hp4
    have h := (hQ.side_dist_of_mem D (s := 3) (by omega) (by omega) hp hp4 le_rfl).2
    rw [hlast, wordDist_comm hS] at h
    omega
  have hgap : ∀ s p q : ℕ, s < 4 → s ≠ 0 → c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      wordDist D.alphabet.carrier v (vertex v w p) ≤ T →
      wordDist D.alphabet.carrier v (vertex v w q) ≤ T → q - p ≤ Q := by
    intro s p q hs hs0 hp hpq hq hpT hqT
    exact hQ.index_gap_le_of_near D hmu hs hs0 hp hpq hq hpT hqT
  have hnot_exempt : ∀ i : ℕ, θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w i) →
      ¬ (∃ q : G, Hyperbolic.IsBetween D.alphabet.carrier v q (vertex v w (c 1)) ∧
        wordDist D.alphabet.carrier (vertex v w i) q ≤ θ) := by
    intro i hi ⟨q, hq, hd⟩
    have hbetween : wordDist D.alphabet.carrier v q +
        wordDist D.alphabet.carrier q (vertex v w (c 1)) =
        wordDist D.alphabet.carrier v (vertex v w (c 1)) := hq
    have hcomm := wordDist_comm hS (vertex v w i) q
    have htri := wordDist_triangle hS v q (vertex v w i)
    omega
  have hfront : A ≤ c 2 - c 1 →
      θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w (1 + A)) ∧
      wordDist D.alphabet.carrier v (vertex v w (1 + A)) ≤ A + 1 := by
    intro hlong
    have hscaled : ⌈mu⌉₊ * ((θ + 3) + b) = A := by
      dsimp [A]
      congr 1
      omega
    have hoff := hQ.metric_offset_le D hmu (s := 1) (T := θ + 3)
      (by omega) (by omega) (p := c 1) (q := 1 + A) le_rfl (by omega)
      (by change 1 + A ≤ c 2; omega)
      (by rw [hscaled]; omega)
    have htri := wordDist_triangle hS (vertex v w (c 1)) v (vertex v w (1 + A))
    have hcomm := wordDist_comm hS (vertex v w (c 1)) v
    have hu := hfirst_upper (1 + A) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  have hback : A ≤ c 4 - c 3 →
      θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w (w.length - A)) ∧
      wordDist D.alphabet.carrier v (vertex v w (w.length - A)) ≤ A := by
    intro hlong
    have hscaled : ⌈mu⌉₊ * ((θ + 3) + b) = A := by
      dsimp [A]
      congr 1
      omega
    have hoff := hQ.metric_offset_le D hmu (s := 3) (T := θ + 3)
      (by omega) (by omega) (p := w.length - A) (q := c 4) (by omega) (by omega) le_rfl
      (by rw [hscaled]; omega)
    rw [hlast, wordDist_comm hS] at hoff
    have hu := hthird_upper (w.length - A) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  by_cases hlong1 : A ≤ c 2 - c 1
  · obtain ⟨hmoff, hmup⟩ := hfront hlong1
    obtain ⟨p, hmp, hpr⟩ := (hthin1 (1 + A) (by omega) (by omega)).resolve_right
      (hnot_exempt _ hmoff)
    have hpT : wordDist D.alphabet.carrier v (vertex v w p) ≤ T := by
      have htri := wordDist_triangle hS v (vertex v w (1 + A)) (vertex v w p)
      dsimp [T]
      omega
    by_cases hlong3 : A ≤ c 4 - c 3
    · rcases hpr with ⟨hp2, hp3⟩ | ⟨hp3, hp4⟩
      · obtain ⟨hjoff, hjup⟩ := hback hlong3
        obtain ⟨p', hjp, hpr'⟩ :=
          (hthin3 (w.length - A) (by omega) (by omega)).resolve_right (hnot_exempt _ hjoff)
        have hp'T : wordDist D.alphabet.carrier v (vertex v w p') ≤ T := by
          have htri := wordDist_triangle hS v (vertex v w (w.length - A)) (vertex v w p')
          dsimp [T]
          omega
        have hpj : wordDist D.alphabet.carrier (vertex v w p')
            (vertex v w (w.length - A)) ≤ θ := by
          rwa [wordDist_comm hS]
        rcases hpr' with ⟨hp'1, hp'2⟩ | ⟨hp'2, hp'3⟩
        · have hg := hgap 1 (c 1) p' (by omega) (by omega) le_rfl hp'1 hp'2
            (by dsimp [T]; omega) hp'T
          apply short_cycle_of_indices D lam v hQ.letters hQ.closed hcomp hiso
            (m := p') (j := w.length - A) (by omega) (by omega) hpj (Or.inr hjoff)
          dsimp [L]
          omega
        · obtain ⟨r, hrlet, hrval, hrlen, hrcos⟩ := exists_connector D lam v hmp (Or.inl hmoff)
          obtain ⟨r', hr'let, hr'val, hr'len, hr'cos⟩ := exists_connector D lam v hpj (Or.inr hjoff)
          by_cases horder : p ≤ p'
          · have hg := hgap 2 p p' (by omega) (by omega) hp2 horder hp'3 hpT hp'T
            obtain ⟨q, hqlet, hqcl, hqlen, hqcomp, hqiso, hqspan⟩ :=
              cycle_of_two_connectors D lam v hQ.letters hQ.closed hcomp hiso
                (m := 1 + A) (j₁ := p) (m₂ := p') (j₂ := w.length - A)
                (by omega) horder (by omega) (by omega) hrlet hrval hrcos hr'let hr'val hr'cos
            refine ⟨q, hqlet, hqcl, ?_, hqcomp, hqiso, hqspan⟩
            dsimp [L]
            omega
          · have hg := hgap 2 p' p (by omega) (by omega) hp'2 (by omega) hp3 hp'T hpT
            obtain ⟨q, hqlet, hqcl, hqlen, hqcomp, hqiso, hqspan⟩ :=
              cycle_of_reversed_splice D hsymm lam v hQ.letters hQ.closed hcomp hiso
                (m := 1 + A) (j := p') (m' := p) (j' := w.length - A)
                (by omega) (by omega) (by omega) (by omega) hrlet hrval hrcos hr'let hr'val hr'cos
            refine ⟨q, hqlet, hqcl, ?_, hqcomp, hqiso, hqspan⟩
            dsimp [L]
            omega
      · have hg := hgap 3 p (c 4) (by omega) (by omega) hp3 hp4 le_rfl hpT
          (by dsimp [T]; omega)
        apply short_cycle_of_indices D lam v hQ.letters hQ.closed hcomp hiso
          (m := 1 + A) (j := p) (by omega) (by omega) hmp (Or.inl hmoff)
        dsimp [L]
        omega
    · have hcorner : wordDist D.alphabet.carrier v (vertex v w (c 3)) ≤ T := by
        have hu := hthird_upper (c 3) le_rfl h34
        dsimp [T]
        omega
      have htail : w.length - p ≤ A + Q := by
        rcases hpr with ⟨hp2, hp3⟩ | ⟨hp3, hp4⟩
        · have hg := hgap 2 p (c 3) (by omega) (by omega) hp2 hp3 le_rfl hpT hcorner
          omega
        · omega
      have hp2 : c 2 ≤ p := by rcases hpr with h | h <;> omega
      have hp4 : p ≤ c 4 := by rcases hpr with h | h <;> omega
      apply short_cycle_of_indices D lam v hQ.letters hQ.closed hcomp hiso
        (m := 1 + A) (j := p) (by omega) (by omega) hmp (Or.inl hmoff)
      dsimp [L]
      omega
  · have hcorner : wordDist D.alphabet.carrier v (vertex v w (c 2)) ≤ T := by
      have hu := hfirst_upper (c 2) h12 le_rfl
      dsimp [T]
      omega
    by_cases hlong3 : A ≤ c 4 - c 3
    · obtain ⟨hjoff, hjup⟩ := hback hlong3
      obtain ⟨p, hjp, hpr⟩ :=
        (hthin3 (w.length - A) (by omega) (by omega)).resolve_right (hnot_exempt _ hjoff)
      have hpT : wordDist D.alphabet.carrier v (vertex v w p) ≤ T := by
        have htri := wordDist_triangle hS v (vertex v w (w.length - A)) (vertex v w p)
        dsimp [T]
        omega
      have hprefix : p ≤ 1 + A + Q := by
        rcases hpr with ⟨hp1, hp2⟩ | ⟨hp2, hp3⟩
        · omega
        · have hg := hgap 2 (c 2) p (by omega) (by omega) le_rfl hp2 hp3 hcorner hpT
          omega
      have hp3 : p ≤ c 3 := by rcases hpr with h | h <;> omega
      have hpj : wordDist D.alphabet.carrier (vertex v w p)
          (vertex v w (w.length - A)) ≤ θ := by rwa [wordDist_comm hS]
      apply short_cycle_of_indices D lam v hQ.letters hQ.closed hcomp hiso
        (m := p) (j := w.length - A) (by omega) (by omega) hpj (Or.inr hjoff)
      dsimp [L]
      omega
    · have hcorner3 : wordDist D.alphabet.carrier v (vertex v w (c 3)) ≤ T := by
        have hu := hthird_upper (c 3) le_rfl h34
        dsimp [T]
        omega
      have hg := hgap 2 (c 2) (c 3) (by omega) (by omega) le_rfl h23 le_rfl hcorner hcorner3
      refine ⟨w, hQ.letters, hQ.closed, ?_, hcomp, hiso, rfl⟩
      dsimp [L]
      omega

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.exists_short_isolating_cycleAt_of_unit
