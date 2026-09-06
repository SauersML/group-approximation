import GroupApproximation.GGT.DGOLemma421MinimalityExclusion

/-!
# The opposite match is strictly internal

Isolation of the source component excludes matching either of the two
already matched target components. Thus the three-side exclusion produces
an intermediate match on both paths, as required by DGO's minimal-gap proof.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A match of an isolated interior source component cannot be one of the
already matched endpoint components on the other path. -/
theorem DGO421MinimalityFourGonData.opposite_match_internal
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {vp vq : G}
    {lam mu nu : Lambda} {ip1 ip2 iq1 iq2 i j k : ℕ}
    (F : DGO421MinimalityFourGonData D vp vq P Q lam mu ip1 ip2 iq1 iq2)
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW3Q : WWord.IsWThree D Q)
    (hnearP : IsComp lam P ip1 (ip1 + 1)) (hfarP : IsComp mu P (ip2 - 1) ip2)
    (hnearQ : IsComp lam Q iq1 (iq1 + 1)) (hfarQ : IsComp mu Q (iq2 - 1) iq2)
    (hiso : IsIsolated D.fam nu vp P i)
    (hleft : ip1 < i) (hright : i + 1 < ip2)
    (hcomp : IsComp nu Q j k) (hj : iq1 ≤ j) (hk : k ≤ iq2)
    (hmatch : (vertex vp P i)⁻¹ * vertex vq Q j ∈ D.fam nu) :
    iq1 < j ∧ k < iq2 := by
  constructor
  · by_contra hnot
    have heq : j = iq1 := by omega
    have hlabel : nu = lam := isCompStart_label_unique_421 ⟨k, hcomp⟩
      (by rw [heq]; exact ⟨iq1 + 1, hnearQ⟩)
    subst nu
    have hc : Connected D.fam lam vp P i ip1 := by
      have hm := (D.fam lam).mul_mem hmatch ((D.fam lam).inv_mem F.near_match)
      change (vertex vp P i)⁻¹ * vertex vp P ip1 ∈ D.fam lam
      convert hm using 1
      rw [heq]
      group
    exact hiso.2 ip1 (by omega) ⟨ip1 + 1, hnearP⟩ hc
  · by_contra hnot
    have heq : k = iq2 := by omega
    have hsucc := isComp_succ_of_isWThree hW3Q hcomp
    have hjEq : j = iq2 - 1 := by omega
    have hlabel : nu = mu := isCompStart_label_unique_421 ⟨k, hcomp⟩
      (by rw [hjEq]; exact ⟨iq2, hfarQ⟩)
    subst nu
    have hqSpan := span_mem_fam_of_isComp D vq hletQ hcomp
    have hpSpan := span_mem_fam_of_isComp D vp hletP hfarP
    have hc : Connected D.fam mu vp P i (ip2 - 1) := by
      have hm := (D.fam mu).mul_mem
        ((D.fam mu).mul_mem ((D.fam mu).mul_mem hmatch hqSpan)
          ((D.fam mu).inv_mem F.far_match)) ((D.fam mu).inv_mem hpSpan)
      change (vertex vp P i)⁻¹ * vertex vp P (ip2 - 1) ∈ D.fam mu
      convert hm using 1
      rw [heq]
      group
    exact hiso.2 (ip2 - 1) (by omega) ⟨ip2, hfarP⟩ hc

/-- The minimality quadrilateral produces a match strictly between its two
matched target components. Every hypothesis is local to the two paths,
their components, and the uniform isolated-component projection. -/
theorem DGO421MinimalityFourGonData.exists_internal_opposite_match
    {D : RelGenSet G Lambda} {C : ℕ}
    (hproj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
      IsQuasiGeodesicPolygon D 4 1 n v word →
      ∀ (nu : Lambda) (i k : ℕ), IsComp nu word i k → IsIsolated D.fam nu v word i →
        (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall nu (C * n))
    {P Q : List (RelLetter G Lambda)} {vp vq : G} {lam mu nu : Lambda}
    {ip1 ip2 iq1 iq2 i : ℕ}
    (F : DGO421MinimalityFourGonData D vp vq P Q lam mu ip1 ip2 iq1 iq2)
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (hnearP : IsComp lam P ip1 (ip1 + 1)) (hfarP : IsComp mu P (ip2 - 1) ip2)
    (hnearQ : IsComp lam Q iq1 (iq1 + 1)) (hfarQ : IsComp mu Q (iq2 - 1) iq2)
    (hsource : IsComp nu P i (i + 1)) (hiso : IsIsolated D.fam nu vp P i)
    (hleft : ip1 < i) (hright : i + 1 < ip2)
    (hip2 : ip2 ≤ P.length) (hiq : iq1 ≤ iq2) (hiq2 : iq2 ≤ Q.length)
    (hdeep : (vertex vp P i)⁻¹ * vertex vp P (i + 1) ∉ D.relBall nu (C * 4)) :
    ∃ j k : ℕ, IsComp nu Q j k ∧ iq1 < j ∧ k < iq2 ∧
      (vertex vp P i)⁻¹ * vertex vq Q j ∈ D.fam nu := by
  obtain ⟨j, k, hcomp, hj, hk, hmatch⟩ := F.exists_opposite_match hproj hletP hletQ
    hW3P hW3Q hnearP hfarP hsource hiso hleft hright hip2 hiq hiq2 hdeep
  have hstrict := F.opposite_match_internal hletP hletQ hW3Q hnearP hfarP hnearQ hfarQ
    hiso hleft hright hcomp hj hk hmatch
  exact ⟨j, k, hcomp, hstrict.1, hstrict.2, hmatch⟩

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.opposite_match_internal
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.exists_internal_opposite_match
