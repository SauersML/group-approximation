import GroupApproximation.GGT.DGOThinQuadrangleAt
import GroupApproximation.GGT.DGOShortIsolatingCycleAt

/-!
# General-parameter thinness on both flanks of an exempt component

The same constant works for every polygon and every vertex on either flank.
The conclusion matches the two alternatives consumed by the short-cycle
construction: a vertex on another original side, or a between-point on the
exempt side. The exempt side is allowed to have arbitrary length.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- General `(μ,b)` thinness for the two sides flanking the exempt side,
with one radius chosen before the polygon. -/
theorem exists_quasiGeodesicFourGon_thinness
    (D : RelGenSet G Lambda) (mu : ℝ) (b δ : ℕ) (hmu : 0 < mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ θ : ℕ, ∀ (v : G) (w : List (RelLetter G Lambda)) (c : ℕ → ℕ),
      QuasiGeodesicFourGon D mu b v w c →
        (∀ i : ℕ, c 1 ≤ i → i ≤ c 2 →
          (∃ p : ℕ, wordDist D.alphabet.carrier (vertex v w i) (vertex v w p) ≤ θ ∧
            ((c 2 ≤ p ∧ p ≤ c 3) ∨ (c 3 ≤ p ∧ p ≤ c 4))) ∨
          (∃ q : G, Hyperbolic.IsBetween D.alphabet.carrier v q (vertex v w (c 1)) ∧
            wordDist D.alphabet.carrier (vertex v w i) q ≤ θ)) ∧
        (∀ i : ℕ, c 3 ≤ i → i ≤ c 4 →
          (∃ p : ℕ, wordDist D.alphabet.carrier (vertex v w i) (vertex v w p) ≤ θ ∧
            ((c 1 ≤ p ∧ p ≤ c 2) ∨ (c 2 ≤ p ∧ p ≤ c 3))) ∨
          (∃ q : G, Hyperbolic.IsBetween D.alphabet.carrier v q (vertex v w (c 1)) ∧
            wordDist D.alphabet.carrier (vertex v w i) q ≤ θ)) := by
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound D.alphabet.carrier mu b δ hmu
  refine ⟨2 * R + 8 * δ, ?_⟩
  intro v w c hQ
  have hS := D.alphabet.symmetricGenerating
  have hlast : vertex v w (c 4) = v := by
    rw [hQ.finish, vertex_eq_mul_listVal_take, List.take_length, hQ.closed, mul_one]
  have hsource : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ i : ℕ, c s ≤ i → i ≤ c (s + 1) →
      ∃ p : G, Hyperbolic.IsBetween D.alphabet.carrier
        (vertex v w (c s)) p (vertex v w (c (s + 1))) ∧
          wordDist D.alphabet.carrier (vertex v w i) p ≤ R := by
    intro s hs hs0 i hsi his
    have hcs : c s ≤ c (s + 1) := hQ.mono (Nat.le_succ s)
    obtain ⟨p, hp, hd⟩ :=
      (hR _ _ hS hδ (hQ.quasiGeodesic s hs hs0)).1 (i - c s) (by omega)
    refine ⟨p, ?_, ?_⟩
    · simpa only [Nat.add_zero, show c s + (c (s + 1) - c s) = c (s + 1) by omega]
        using hp
    · simpa only [show c s + (i - c s) = i by omega] using hd
  have htarget : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ q : G,
      Hyperbolic.IsBetween D.alphabet.carrier
        (vertex v w (c s)) q (vertex v w (c (s + 1))) →
      ∃ j : ℕ, c s ≤ j ∧ j ≤ c (s + 1) ∧
        wordDist D.alphabet.carrier q (vertex v w j) ≤ R := by
    intro s hs hs0 q hq
    have hcs : c s ≤ c (s + 1) := hQ.mono (Nat.le_succ s)
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c s + 0)) q
        (vertex v w (c s + (c (s + 1) - c s))) := by
      simpa only [Nat.add_zero, show c s + (c (s + 1) - c s) = c (s + 1) by omega]
        using hq
    obtain ⟨j, hj, hd⟩ := (hR _ _ hS hδ (hQ.quasiGeodesic s hs hs0)).2 q hq'
    exact ⟨c s + j, by omega, by omega, hd⟩
  constructor
  · intro i hi1 hi2
    obtain ⟨p, hp, hd⟩ := hsource 1 (by omega) (by omega) i hi1 hi2
    rcases exists_isBetween_of_quadrangle hS hδ hp
        (x₃ := vertex v w (c 3)) (x₄ := v) with
      ⟨q, hq, hdist⟩ | ⟨q, hq, hdist⟩ | ⟨q, hq, hdist⟩
    · obtain ⟨j, hj1, hj2, hnear⟩ := htarget 2 (by omega) (by omega) q hq
      refine Or.inl ⟨j, ?_, Or.inl ⟨hj1, hj2⟩⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      have htri' := wordDist_triangle hS (vertex v w i) q (vertex v w j)
      omega
    · have hq' : Hyperbolic.IsBetween D.alphabet.carrier
          (vertex v w (c 3)) q (vertex v w (c 4)) := by simpa only [hlast] using hq
      obtain ⟨j, hj1, hj2, hnear⟩ := htarget 3 (by omega) (by omega) q hq'
      refine Or.inl ⟨j, ?_, Or.inr ⟨hj1, hj2⟩⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      have htri' := wordDist_triangle hS (vertex v w i) q (vertex v w j)
      omega
    · refine Or.inr ⟨q, hq, ?_⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      omega
  · intro i hi3 hi4
    obtain ⟨p, hp, hd⟩ := hsource 3 (by omega) (by omega) i hi3 hi4
    change Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c 3)) p
      (vertex v w (c 4)) at hp
    rw [hlast] at hp
    rcases exists_isBetween_of_quadrangle hS hδ hp
        (x₃ := vertex v w (c 1)) (x₄ := vertex v w (c 2)) with
      ⟨q, hq, hdist⟩ | ⟨q, hq, hdist⟩ | ⟨q, hq, hdist⟩
    · refine Or.inr ⟨q, hq, ?_⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      omega
    · obtain ⟨j, hj1, hj2, hnear⟩ := htarget 1 (by omega) (by omega) q hq
      refine Or.inl ⟨j, ?_, Or.inl ⟨hj1, hj2⟩⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      have htri' := wordDist_triangle hS (vertex v w i) q (vertex v w j)
      omega
    · obtain ⟨j, hj1, hj2, hnear⟩ := htarget 2 (by omega) (by omega) q hq
      refine Or.inl ⟨j, ?_, Or.inr ⟨hj1, hj2⟩⟩
      have htri := wordDist_triangle hS (vertex v w i) p q
      have htri' := wordDist_triangle hS (vertex v w i) q (vertex v w j)
      omega

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.exists_quasiGeodesicFourGon_thinness
