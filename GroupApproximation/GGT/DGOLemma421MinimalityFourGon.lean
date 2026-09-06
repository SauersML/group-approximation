import GroupApproximation.GGT.DGOLemma421Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The minimality quadrilateral at the actual path basepoints

DGO Lemma 4.21(b) compares paths with different basepoints. This module
constructs the quadrilateral between two matched pairs without resetting
those basepoints. The connector-value equations and closing equation travel
with the polygon, since the component-exclusion argument needs them.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The two vertex-difference connectors close the quadrilateral even when
the paths have different basepoints. -/
theorem listVal_minimalityFourGon_closes_at
    {P Q e f : List (RelLetter G Lambda)} {vp vq : G}
    {ip1 ip2 iq1 iq2 : ℕ} (hip : ip1 ≤ ip2) (hiq : iq1 ≤ iq2)
    (he : RelLetter.listVal e = (vertex vq Q iq1)⁻¹ * vertex vp P ip1)
    (hf : RelLetter.listVal f = (vertex vp P ip2)⁻¹ * vertex vq Q iq2) :
    RelLetter.listVal ((Q.drop iq1).take (iq2 - iq1)) =
      RelLetter.listVal e * RelLetter.listVal ((P.drop ip1).take (ip2 - ip1)) *
        RelLetter.listVal f := by
  have hP := mul_listVal_take_drop vp P ip1 (ip2 - ip1)
  have hQ := mul_listVal_take_drop vq Q iq1 (iq2 - iq1)
  rw [show ip1 + (ip2 - ip1) = ip2 by omega] at hP
  rw [show iq1 + (iq2 - iq1) = iq2 by omega] at hQ
  have hPseg : RelLetter.listVal ((P.drop ip1).take (ip2 - ip1)) =
      (vertex vp P ip1)⁻¹ * vertex vp P ip2 := by
    rw [← hP]
    group
  have hQseg : RelLetter.listVal ((Q.drop iq1).take (iq2 - iq1)) =
      (vertex vq Q iq1)⁻¹ * vertex vq Q iq2 := by
    rw [← hQ]
    group
  rw [hQseg, he, hPseg, hf]
  group

/-- The polygon and the actual connector equations needed to exclude
connections to its two short sides. -/
structure DGO421MinimalityFourGonData
    (D : RelGenSet G Lambda) (vp vq : G) (P Q : List (RelLetter G Lambda))
    (lam mu : Lambda) (ip1 ip2 iq1 iq2 : ℕ) where
  near : List (RelLetter G Lambda)
  far : List (RelLetter G Lambda)
  near_length : near.length ≤ 1
  far_length : far.length ≤ 1
  near_labels : ∀ letter ∈ near, letter.IsCompOf lam
  far_labels : ∀ letter ∈ far, letter.IsCompOf mu
  near_match : (vertex vp P ip1)⁻¹ * vertex vq Q iq1 ∈ D.fam lam
  far_match : (vertex vp P ip2)⁻¹ * vertex vq Q iq2 ∈ D.fam mu
  near_value : RelLetter.listVal near = (vertex vq Q iq1)⁻¹ * vertex vp P ip1
  far_value : RelLetter.listVal far = (vertex vp P ip2)⁻¹ * vertex vq Q iq2
  closes : RelLetter.listVal ((Q.drop iq1).take (iq2 - iq1)) =
    RelLetter.listVal near * RelLetter.listVal ((P.drop ip1).take (ip2 - ip1)) *
      RelLetter.listVal far
  polygon : IsQuasiGeodesicPolygon D 4 1 4 (1 : G)
    (near ++ (P.drop ip1).take (ip2 - ip1) ++ far ++
      revWord ((Q.drop iq1).take (iq2 - iq1)))

/-- Construct the minimality quadrilateral from two matched pairs and the
quasi-geodesic estimates of Lemma 4.21(a). -/
theorem exists_minimalityFourGon_at
    (D : RelGenSet G Lambda) (hbase : DGO421BaseSymmetric D)
    {P Q : List (RelLetter G Lambda)} {vp vq : G} {lam mu : Lambda}
    {ip1 ip2 iq1 iq2 : ℕ}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hm1 : (vertex vp P ip1)⁻¹ * vertex vq Q iq1 ∈ D.fam lam)
    (hm2 : (vertex vp P ip2)⁻¹ * vertex vq Q iq2 ∈ D.fam mu)
    (hip : ip1 ≤ ip2) (hiq : iq1 ≤ iq2)
    (hip2 : ip2 ≤ P.length) (hiq2 : iq2 ≤ Q.length)
    (hqgP : ∀ i j : ℕ, i ≤ j → j ≤ P.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P i) (vertex vp P j) : ℝ))
    (hqgQ : ∀ i j : ℕ, i ≤ j → j ≤ Q.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q i) (vertex vq Q j) : ℝ)) :
    Nonempty (DGO421MinimalityFourGonData D vp vq P Q lam mu ip1 ip2 iq1 iq2) := by
  have hnear : (vertex vq Q iq1)⁻¹ * vertex vp P ip1 ∈ D.fam lam := by
    simpa only [mul_inv_rev, inv_inv] using (D.fam lam).inv_mem hm1
  obtain ⟨e, hge, heLength, heLabels⟩ :=
    exists_isGeodesicWord_peripheralConnector D lam (vertex vq Q iq1) _ hnear
  obtain ⟨f, hgf, hfLength, hfLabels⟩ :=
    exists_isGeodesicWord_peripheralConnector D mu (vertex vp P ip2) _ hm2
  have heValue : RelLetter.listVal e = (vertex vq Q iq1)⁻¹ * vertex vp P ip1 :=
    mul_left_cancel hge.2.1
  have hfValue : RelLetter.listVal f = (vertex vp P ip2)⁻¹ * vertex vq Q iq2 :=
    mul_left_cancel hgf.2.1
  have hclose := listVal_minimalityFourGon_closes_at hip hiq heValue hfValue
  have hqgPone := quasiGeodesic_segment_of_quasiGeodesic D
    (v := vp) (k := 0) (m := P.length) (by omega) hqgP
  have hqgQone := quasiGeodesic_segment_of_quasiGeodesic D
    (v := vq) (k := 0) (m := Q.length) (by omega) hqgQ
  simp only [List.drop_zero, List.take_length] at hqgPone hqgQone
  refine ⟨{
    near := e
    far := f
    near_length := heLength
    far_length := hfLength
    near_labels := heLabels
    far_labels := hfLabels
    near_match := hm1
    far_match := hm2
    near_value := heValue
    far_value := hfValue
    closes := hclose
    polygon := ?_ }⟩
  exact isQuasiGeodesicPolygon_minimalityFourGon D hbase hletP hletQ hge.1 hgf.1
    (isGeodesicWord_one_of_isGeodesicWord hge)
    (isGeodesicWord_one_of_isGeodesicWord hgf)
    (by omega) (by omega) hqgPone hqgQone hclose

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.listVal_minimalityFourGon_closes_at
#audit_axioms GroupApproximation.GGT.OsinComponents.exists_minimalityFourGon_at
