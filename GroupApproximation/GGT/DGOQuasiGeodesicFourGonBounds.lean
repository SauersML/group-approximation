import GroupApproximation.GGT.DGOQuasiGeodesicFourGonThinness

/-!
# Metric and index bounds for general quasi-geodesic four-gons

The corner-offset argument needs index bounds with the multiplicative constant
retained. These estimates give the ceiling-scaled bound and its consequence
for two vertices in a fixed ball, without changing the original side paths.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The two chain inequalities, expressed at original word indices. -/
theorem QuasiGeodesicFourGon.side_dist_of_mem
    (D : RelGenSet G Lambda) {mu : ℝ} {b : ℕ} {v : G}
    {w : List (RelLetter G Lambda)} {c : ℕ → ℕ}
    (hQ : QuasiGeodesicFourGon D mu b v w c)
    {s p q : ℕ} (hs : s < 4) (hs0 : s ≠ 0)
    (hp : c s ≤ p) (hpq : p ≤ q) (hq : q ≤ c (s + 1)) :
    ((q - p : ℕ) : ℝ) / mu - (b : ℝ) ≤
        (wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℝ) ∧
      wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) ≤ q - p := by
  have h := hQ.quasiGeodesic s hs hs0 (p - c s) (q - c s) (by omega) (by omega)
  simpa only [show c s + (p - c s) = p by omega,
    show c s + (q - c s) = q by omega,
    show q - c s - (p - c s) = q - p by omega] using h

/-- A metric distance controls the side's index distance with factor `⌈μ⌉₊`. -/
theorem QuasiGeodesicFourGon.index_gap_le
    (D : RelGenSet G Lambda) {mu : ℝ} {b : ℕ} {v : G}
    {w : List (RelLetter G Lambda)} {c : ℕ → ℕ}
    (hQ : QuasiGeodesicFourGon D mu b v w c) (hmu : 0 < mu)
    {s p q : ℕ} (hs : s < 4) (hs0 : s ≠ 0)
    (hp : c s ≤ p) (hpq : p ≤ q) (hq : q ≤ c (s + 1)) :
    q - p ≤ ⌈mu⌉₊ * (wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) + b) := by
  have h := ((hQ.quasiGeodesic s hs hs0).toQuasiGeodesic hmu)
    (p - c s) (by omega) (q - c s) (by omega) (by omega)
  simpa only [show c s + (p - c s) = p by omega,
    show c s + (q - c s) = q by omega,
    show q - c s - (p - c s) = q - p by omega] using h.2

/-- Two vertices of one side in a radius-`T` ball are at bounded index distance. -/
theorem QuasiGeodesicFourGon.index_gap_le_of_near
    (D : RelGenSet G Lambda) {mu : ℝ} {b : ℕ} {v : G}
    {w : List (RelLetter G Lambda)} {c : ℕ → ℕ}
    (hQ : QuasiGeodesicFourGon D mu b v w c) (hmu : 0 < mu)
    {s p q T : ℕ} (hs : s < 4) (hs0 : s ≠ 0)
    (hp : c s ≤ p) (hpq : p ≤ q) (hq : q ≤ c (s + 1))
    (hpT : wordDist D.alphabet.carrier v (vertex v w p) ≤ T)
    (hqT : wordDist D.alphabet.carrier v (vertex v w q) ≤ T) :
    q - p ≤ ⌈mu⌉₊ * (2 * T + b) := by
  have hgap := hQ.index_gap_le D hmu hs hs0 hp hpq hq
  have htri := wordDist_triangle D.alphabet.symmetricGenerating (vertex v w p) v
    (vertex v w q)
  have hcomm := wordDist_comm D.alphabet.symmetricGenerating (vertex v w p) v
  exact hgap.trans (Nat.mul_le_mul_left _ (by omega))

/-- A ceiling-scaled index offset gives the required metric offset. -/
theorem QuasiGeodesicFourGon.metric_offset_le
    (D : RelGenSet G Lambda) {mu : ℝ} {b : ℕ} {v : G}
    {w : List (RelLetter G Lambda)} {c : ℕ → ℕ}
    (hQ : QuasiGeodesicFourGon D mu b v w c) (hmu : 0 < mu)
    {s p q T : ℕ} (hs : s < 4) (hs0 : s ≠ 0)
    (hp : c s ≤ p) (hpq : p ≤ q) (hq : q ≤ c (s + 1))
    (hoff : ⌈mu⌉₊ * (T + b) ≤ q - p) :
    T ≤ wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) := by
  have hK : 0 < ⌈mu⌉₊ := Nat.one_le_ceil_iff.mpr hmu
  have hgap := hQ.index_gap_le D hmu hs hs0 hp hpq hq
  have h := Nat.le_of_mul_le_mul_left (hoff.trans hgap) hK
  omega

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.QuasiGeodesicFourGon.side_dist_of_mem
#audit_axioms GroupApproximation.GGT.OsinComponents.QuasiGeodesicFourGon.index_gap_le
#audit_axioms GroupApproximation.GGT.OsinComponents.QuasiGeodesicFourGon.index_gap_le_of_near
#audit_axioms GroupApproximation.GGT.OsinComponents.QuasiGeodesicFourGon.metric_offset_le
