import GroupApproximation.GGT.DGOLemma421LocatedAbsorption
import GroupApproximation.GGT.DGOPolygonGeodesicChain

/-!
# Forward matches from separated source positions

A peripheral coset match connects its two path vertices by at most one edge.
The quasi-geodesic estimate and initial endpoint closeness therefore compare
the two word positions. Widely separated source positions force their target
positions to occur in forward order.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The target position of a coset match is controlled by its source position
and the initial endpoint distance. -/
theorem target_position_le_of_cosetMatch
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {vp vq : G}
    {nu : Lambda} {i j E : ℕ}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hi : i ≤ P.length) (hj : j ≤ Q.length)
    (hstart : (wordDist D.alphabet.carrier vp vq : ℝ) ≤ E)
    (hqgQ : ∀ a b : ℕ, a ≤ b → b ≤ Q.length →
      ((b - a : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q a) (vertex vq Q b) : ℝ))
    (hmatch : (vertex vp P i)⁻¹ * vertex vq Q j ∈ D.fam nu) :
    j ≤ 4 * (E + i + 2) := by
  have hpath := wordDist_vertex_le' D hletP vp (Nat.zero_le i) hi
  simp only [vertex_zero, Nat.sub_zero] at hpath
  have hedge := wordDist_le_one_of_mem_fam D hmatch
  have hstartNat : wordDist D.alphabet.carrier vq vp ≤ E := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact_mod_cast hstart
  have htri1 := wordDist_triangle D.alphabet.symmetricGenerating vq vp (vertex vq Q j)
  have htri2 := wordDist_triangle D.alphabet.symmetricGenerating vp (vertex vp P i) (vertex vq Q j)
  have hupper : wordDist D.alphabet.carrier vq (vertex vq Q j) ≤ E + i + 1 := by omega
  have hupperReal : (wordDist D.alphabet.carrier vq (vertex vq Q j) : ℝ) ≤
      (E : ℝ) + (i : ℝ) + 1 := by exact_mod_cast hupper
  have hqg := hqgQ 0 j (Nat.zero_le j) hj
  simp only [vertex_zero, Nat.sub_zero] at hqg
  have hbound : (j : ℝ) ≤ 4 * ((E : ℝ) + (i : ℝ) + 2) := by linarith
  exact_mod_cast hbound

/-- Quantitatively separated source matches occur in forward target order.
This uses only quasi-geodesicity, initial closeness, and their coset matches. -/
theorem target_position_lt_of_separated_source_matches
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {vp vq : G}
    {lam mu : Lambda} {i₁ i₂ j₁ j₂ E : ℕ}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hi₁ : i₁ ≤ P.length) (hi₂ : i₂ ≤ P.length)
    (hj₁ : j₁ ≤ Q.length) (hj₂ : j₂ ≤ Q.length)
    (hstart : (wordDist D.alphabet.carrier vp vq : ℝ) ≤ E)
    (hqgP : ∀ a b : ℕ, a ≤ b → b ≤ P.length →
      ((b - a : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P a) (vertex vp P b) : ℝ))
    (hqgQ : ∀ a b : ℕ, a ≤ b → b ≤ Q.length →
      ((b - a : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q a) (vertex vq Q b) : ℝ))
    (hmatch₁ : (vertex vp P i₁)⁻¹ * vertex vq Q j₁ ∈ D.fam lam)
    (hmatch₂ : (vertex vp P i₂)⁻¹ * vertex vq Q j₂ ∈ D.fam mu)
    (hgap : 16 * i₁ + 20 * E + 40 < i₂) : j₁ < j₂ := by
  have hfirst := target_position_le_of_cosetMatch hletP hi₁ hj₁ hstart hqgQ hmatch₁
  have hstart' : (wordDist D.alphabet.carrier vq vp : ℝ) ≤ E := by
    rwa [wordDist_comm D.alphabet.symmetricGenerating]
  have hmatch₂' : (vertex vq Q j₂)⁻¹ * vertex vp P i₂ ∈ D.fam mu := by
    simpa only [mul_inv_rev, inv_inv] using (D.fam mu).inv_mem hmatch₂
  have hsecond := target_position_le_of_cosetMatch hletQ hj₂ hi₂ hstart' hqgP hmatch₂'
  omega

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.target_position_le_of_cosetMatch
#audit_axioms GroupApproximation.GGT.OsinComponents.target_position_lt_of_separated_source_matches
