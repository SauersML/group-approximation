import GroupApproximation.GGT.DGOProposition414GeneralInput

/-!
# Finiteness and extremal polygons at general DGO parameters

The proved general four-gon bound propagates to every side count. Summing
that bound gives a finite initial cost; it is not the uniform linear bound.
Minimization and the extremal-input principle therefore apply at the genuine
parameters without appealing to an additive comparison.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- A bound at one side count for all genuine general-parameter inputs. -/
def QuasiSumBound (D : RelGenSet G Λ) (mu b : ℝ) (n K : ℕ) : Prop :=
  ∀ P : QuasiSumBoundInput D mu b n, P.HasRadiusWitnessAtMost K

/-- Increasing the radius allowance preserves the bound. -/
theorem QuasiSumBound.mono {D : RelGenSet G Λ} {mu b : ℝ} {n K K' : ℕ}
    (h : QuasiSumBound D mu b n K) (hle : K ≤ K') :
    QuasiSumBound D mu b n K' := by
  intro P
  obtain ⟨r, hr, hsum⟩ := h P
  exact ⟨r, hr, hsum.trans hle⟩

/-- A finite sum bound exists at every side count for every `mu ≥ 1`. -/
theorem exists_quasiSumBound (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    ∃ K : ℕ, QuasiSumBound D mu (b : ℝ) n K := by
  have hmu0 : 0 < mu := lt_of_lt_of_le zero_lt_one hmu
  obtain ⟨C, hC⟩ := exists_isolatedComponentBound_quasiGeodesicFourGon
    D hsymm mu (b + 1) δ hmu0 hδ
  have hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - (b + 1 : ℕ)
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4) := by
    intro v w c hlet hclosed hc0 hc4 hcmono lam hquasi hcomp hiso
    have hQ : QuasiGeodesicFourGon D mu (b + 1) v w c := by
      refine ⟨hlet, hclosed, hc0, hc4, monotone_nat_of_le_succ hcmono, ?_⟩
      intro s hs hs0 p q hpq hq
      have hstep := hcmono s
      have hprogress := hquasi s hs hs0 (c s + p) (c s + q)
        (by omega) (by omega) (by omega)
      refine ⟨by simpa only [Nat.add_sub_add_left] using hprogress, ?_⟩
      have hmono := monotone_nat_of_le_succ hcmono
      have hfinish : c (s + 1) ≤ w.length := by
        rw [← hc4]
        exact hmono (by omega)
      have hupper := wordDist_vertex_le' D hlet v
        (show c s + p ≤ c s + q by omega)
        (show c s + q ≤ w.length by omega)
      simpa only [Nat.add_sub_add_left] using hupper
    exact relBall_mono_radius D lam (by omega) (hC lam v w c hQ hcomp hiso)
  let R := (n + 1) * C * (n + 2)
  refine ⟨n * R, ?_⟩
  intro P
  have hpoly : IsQuasiGeodesicPolygon D mu ((b + 1 : ℕ) : ℝ)
      n P.basepoint P.word := by
    simpa only [Nat.cast_add, Nat.cast_one] using P.toPolygon hmu (Nat.cast_nonneg b)
  refine ⟨fun _ => R, ?_, ?_⟩
  · intro s hs
    exact isolatedComponentBound_nGon_of_baseCase D hsymm mu (b + 1 : ℕ)
      hmu (Nat.cast_nonneg _) C hbase n P.basepoint P.word hpoly
      (P.label s) (P.cut s) (P.cut (s + 1))
      (P.target_component s hs) (P.target_isolated s hs)
  · have hsubset : P.target ⊆ Finset.range n := by
      intro s hs
      exact Finset.mem_range.mpr (P.target_lt s hs)
    have hcard : P.target.card ≤ n := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    rw [Finset.sum_const_nat (fun _ _ => rfl)]
    exact Nat.mul_le_mul_right R hcard

/-- Least admissible sum at the genuine general parameters. -/
noncomputable def quasiSumCost (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_quasiSumBound D hsymm mu b hmu hδ n)

/-- The least general-parameter sum bound is attained. -/
theorem quasiSumBound_quasiSumCost (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (n : ℕ) :
    QuasiSumBound D mu (b : ℝ) n (quasiSumCost D hsymm mu b hmu hδ n) := by
  classical
  exact Nat.find_spec (exists_quasiSumBound D hsymm mu b hmu hδ n)

/-- Minimality of the general-parameter sum cost. -/
theorem quasiSumCost_le (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n K : ℕ} (hK : QuasiSumBound D mu (b : ℝ) n K) :
    quasiSumCost D hsymm mu b hmu hδ n ≤ K := by
  classical
  exact Nat.find_min' (exists_quasiSumBound D hsymm mu b hmu hδ n) hK

/-- A positive least cost has an extremal polygon. The child tuple can thus
be chosen from that particular polygon in the numerical subdivision proof. -/
theorem exists_extremal_quasiSumBoundInput_of_pos (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (n : ℕ) (hpos : 0 < quasiSumCost D hsymm mu b hmu hδ n) :
    ∃ P : QuasiSumBoundInput D mu (b : ℝ) n,
      ∀ r : ℕ → ℕ,
        (∀ s ∈ P.target, P.span s ∈ D.relBall (P.label s) (r s)) →
        quasiSumCost D hsymm mu b hmu hδ n ≤ ∑ s ∈ P.target, r s := by
  classical
  let K := quasiSumCost D hsymm mu b hmu hδ n
  have hnot : ¬ QuasiSumBound D mu (b : ℝ) n (K - 1) := by
    intro hsmall
    have hle : K ≤ K - 1 := quasiSumCost_le D hsymm mu b hmu hδ hsmall
    dsimp [K] at hle
    omega
  unfold QuasiSumBound QuasiSumBoundInput.HasRadiusWitnessAtMost at hnot
  push Not at hnot
  obtain ⟨P, hP⟩ := hnot
  refine ⟨P, ?_⟩
  intro r hr
  have hgt := hP r hr
  dsimp [K] at hgt
  omega

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_quasiSumBound
#audit_axioms GroupApproximation.GGT.DGOProposition414.quasiSumBound_quasiSumCost
#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_extremal_quasiSumBoundInput_of_pos
