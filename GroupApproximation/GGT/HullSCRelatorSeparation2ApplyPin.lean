import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyGap

/-!
# The match is pinned near the diagonal, for sides that are only quasi-geodesic

`GGT.OsinComponents.index_le_of_connector` pins a match to within `eps + 1` of
the diagonal, and reads `wordNorm (vertex 1 q i) = i` off the side being
GEODESIC.  The quadrilateral of this chain has sides that are only
`(1, b)`-quasi-geodesic, where that identity fails in both directions, and the
mixed cases need the pinning: without it there is no ORDER between the two
matches, and `HullSC.false_of_span_mixed` asks for `j₁ < j₂`.

What survives is the same statement with `b` added.  A quasi-geodesic side gives
`i - b ≤ wordNorm (vertex 1 q i) ≤ i` -- the upper half from
`wordDist_vertex_le`, which holds of any admissible word because the segment
between two indices spells the difference, and the lower half from the
quasi-geodesic clause at `0` and `i`.  The two triangle inequalities then run
exactly as in the geodesic case, the connector costing one letter because it
lies in `H_λ`.

`lt_of_two_connectors_qg` is what the mixed cases actually call: two matches
whose sources are more than `2(eps + 1 + b)` apart land in the same order.  One
match alone is consistent with an inversion, which is why the two-block form is
the one the mixed cases need; the separation constant is where `(C2)` of the
construction's clauses comes from.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

section Pin

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex of a quasi-geodesic side has word length between `i - b` and
`i`.** -/
theorem wordNorm_vertex_qg (D : RelGenSet G Λ) {q : List (RelLetter G Λ)}
    {bb : ℝ} {Bn i : ℕ} (hlet : ∀ a ∈ q, D.IsLetter a)
    (hqg : ∀ x y : ℕ, x ≤ y → y ≤ q.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q x)
              (vertex (1 : G) q y) : ℕ) : ℝ))
    (hB : bb ≤ (Bn : ℝ)) (hi : i ≤ q.length) :
    wordNorm D.alphabet.carrier (vertex (1 : G) q i) ≤ i ∧
      i ≤ wordNorm D.alphabet.carrier (vertex (1 : G) q i) + Bn := by
  constructor
  · have h := wordDist_vertex_le D hlet (Nat.zero_le i) hi
    rw [vertex_zero, wordDist_one_left] at h
    omega
  · have h := le_of_qg_one (hqg 0 i (Nat.zero_le i) hi) hB
    rw [vertex_zero, wordDist_one_left] at h
    omega

/-- **The match is pinned near the diagonal**, for quasi-geodesic sides.

`GGT.OsinComponents.index_le_of_connector` with `eps + 1` replaced by
`eps + 1 + b`; both directions are the triangle inequality for `wordNorm`, the
reverse one after inverting the connector equation. -/
theorem index_le_of_connector_qg (D : RelGenSet G Λ) {lam : Λ}
    {p q s : List (RelLetter G Λ)} {bb : ℝ} {Bn eps i j : ℕ}
    (hqlet : ∀ a ∈ q, D.IsLetter a) (hslet : ∀ a ∈ s, D.IsLetter a)
    (hqg : ∀ x y : ℕ, x ≤ y → y ≤ q.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q x)
              (vertex (1 : G) q y) : ℕ) : ℝ))
    (hsg : ∀ x y : ℕ, x ≤ y → y ≤ s.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) s x)
              (vertex (1 : G) s y) : ℕ) : ℝ))
    (hB : bb ≤ (Bn : ℝ)) (hi : i ≤ q.length) (hj : j ≤ s.length)
    (hple : wordNorm D.alphabet.carrier (RelLetter.listVal p) ≤ eps)
    {h : G} (hh : h ∈ D.fam lam)
    (heq : RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s j) :
    j ≤ i + eps + 1 + Bn ∧ i ≤ j + eps + 1 + Bn := by
  have hsym := D.alphabet.symmetricGenerating
  obtain ⟨hqu, hql⟩ := wordNorm_vertex_qg D hqlet hqg hB hi
  obtain ⟨hsu, hsl⟩ := wordNorm_vertex_qg D hslet hsg hB hj
  have hh1 : wordNorm D.alphabet.carrier h ≤ 1 :=
    wordNorm_connector_le_one D hh
  constructor
  · have hA : wordNorm D.alphabet.carrier (vertex (1 : G) s j)
        ≤ wordNorm D.alphabet.carrier
            (RelLetter.listVal p * vertex (1 : G) q i)
          + wordNorm D.alphabet.carrier h := by
      rw [← heq]
      exact wordNorm_mul_le hsym _ _
    have hA2 : wordNorm D.alphabet.carrier
        (RelLetter.listVal p * vertex (1 : G) q i)
        ≤ wordNorm D.alphabet.carrier (RelLetter.listVal p)
          + wordNorm D.alphabet.carrier (vertex (1 : G) q i) :=
      wordNorm_mul_le hsym _ _
    omega
  · have hback : vertex (1 : G) q i
        = (RelLetter.listVal p)⁻¹ * vertex (1 : G) s j * h⁻¹ := by
      rw [← heq]
      group
    have hC2 : wordNorm D.alphabet.carrier (vertex (1 : G) q i)
        ≤ wordNorm D.alphabet.carrier
            ((RelLetter.listVal p)⁻¹ * vertex (1 : G) s j)
          + wordNorm D.alphabet.carrier h⁻¹ := by
      rw [hback]
      exact wordNorm_mul_le hsym _ _
    have hD2 : wordNorm D.alphabet.carrier
        ((RelLetter.listVal p)⁻¹ * vertex (1 : G) s j)
        ≤ wordNorm D.alphabet.carrier ((RelLetter.listVal p)⁻¹)
          + wordNorm D.alphabet.carrier (vertex (1 : G) s j) :=
      wordNorm_mul_le hsym _ _
    rw [wordNorm_inv hsym] at hC2
    rw [wordNorm_inv hsym] at hD2
    omega

/-- **Two matches whose sources are far apart land in the same order.**

The pinning puts each `j` within `eps + 1 + b` of its `i`, so a separation of
more than twice that between the two sources forces the order.  One match alone
is consistent with an inversion, which is why the mixed cases need two. -/
theorem lt_of_two_connectors_qg (D : RelGenSet G Λ) {lam : Λ}
    {p q s : List (RelLetter G Λ)} {bb : ℝ} {Bn eps i₁ i₂ j₁ j₂ : ℕ}
    (hqlet : ∀ a ∈ q, D.IsLetter a) (hslet : ∀ a ∈ s, D.IsLetter a)
    (hqg : ∀ x y : ℕ, x ≤ y → y ≤ q.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q x)
              (vertex (1 : G) q y) : ℕ) : ℝ))
    (hsg : ∀ x y : ℕ, x ≤ y → y ≤ s.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) s x)
              (vertex (1 : G) s y) : ℕ) : ℝ))
    (hB : bb ≤ (Bn : ℝ)) (hi₁ : i₁ ≤ q.length) (hi₂ : i₂ ≤ q.length)
    (hj₁ : j₁ ≤ s.length) (hj₂ : j₂ ≤ s.length)
    (hple : wordNorm D.alphabet.carrier (RelLetter.listVal p) ≤ eps)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam lam) (hh₂ : h₂ ∈ D.fam lam)
    (he₁ : RelLetter.listVal p * vertex (1 : G) q i₁ * h₁
      = vertex (1 : G) s j₁)
    (he₂ : RelLetter.listVal p * vertex (1 : G) q i₂ * h₂
      = vertex (1 : G) s j₂)
    (hsep : i₁ + 2 * (eps + 1 + Bn) < i₂) : j₁ < j₂ := by
  obtain ⟨hA, -⟩ :=
    index_le_of_connector_qg D hqlet hslet hqg hsg hB hi₁ hj₁ hple hh₁ he₁
  obtain ⟨-, hB'⟩ :=
    index_le_of_connector_qg D hqlet hslet hqg hsg hB hi₂ hj₂ hple hh₂ he₂
  omega

end Pin

end OsinComponents
end GGT
end GroupApproximation
