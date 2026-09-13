import GroupApproximation.GGT.HullSCUnconeLemmaB
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: a corner of a geodesic triangle is near the other side

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`), whose hyperbolicity clause
compares a relative Cayley graph `Γ(G, D)` with the Cayley graph of a smaller alphabet `S`.  This
module walks along a short geodesic word of `D` from a vertex of one side of a geodesic triangle to
the other side, and bounds the distance in `Γ(G, S)` from that vertex to the other side
(`corner_near`).  The walk needs only two facts about `S`:

* `hbase` — every base letter of `D` is within one step in `Γ(G, S)`;
* `hball` — the endpoints of a connector in a relative ball of radius `Dc` are within `T` in
  `Γ(G, S)`.

It adapts `GGT/HullSCUnconeLemmaB.lean`, where `S` is the un-coned alphabet of cyclic members.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.Uncone (AvoidsCosetFrom noComp_of_avoidsCosetFrom
  exists_of_not_avoidsCosetFrom avoidsCosetFrom_take_of_isComp avoidsCosetFrom_drop_of_isComp
  avoidsCosetFrom_of_noComp closingJump_located span_mem_relBall_of_noComp
  exitEntranceConnector_mem_relBall geodesicWord_drop exists_near_of_walk
  isComp_succ_of_isCompOf_geodesic)

universe u w

section Corner

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A base letter of a word is one step in `Γ(G, S)`.** -/
theorem wordDist_vertex_succ_le_one_of_not_comp (D : RelGenSet G Λ) {S : Set G}
    (hbase : ∀ b ∈ D.base, wordNorm S b ≤ 1) {f : G} {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) {j : ℕ} (hj : j < w.length)
    (hnot : ∀ (lam : Λ) (e : G), w[j]'hj ≠ RelLetter.comp lam e) :
    wordDist S (vertex f w j) (vertex f w (j + 1)) ≤ 1 := by
  have hl := hlet _ (List.getElem_mem hj)
  have hval : wordNorm S (w[j]'hj).val ≤ 1 := by
    revert hnot hl
    generalize w[j]'hj = a
    intro hnot hl
    cases a with
    | base b => exact hbase b hl
    | comp mu h => exact absurd rfl (hnot mu h)
  unfold wordDist
  rw [vertex_succ w f j hj, inv_mul_cancel_left]
  exact hval

/-- **One step of the walk from a corner vertex toward the other side.** -/
theorem corner_walk_step (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (hbase : ∀ b ∈ D.base, wordNorm S b ≤ 1)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (P : Set G) {X Y Z : G} {W₁ W₂ : List (RelLetter G Λ)}
    (hW₁ : IsGeodesicWord D X Y W₁) (hW₂ : IsGeodesicWord D X Z W₂)
    {k kst : ℕ} (hk : k ≤ W₁.length) (hkst : kst ≤ W₂.length)
    {u : List (RelLetter G Λ)}
    (hu : IsGeodesicWord D (vertex X W₁ k) (vertex X W₂ kst) u)
    (hP₂ : ∀ i ≤ W₂.length, vertex X W₂ i ∈ P)
    (hside : ∀ (lam : Λ) (t : ℕ), t < k → IsComp lam W₁ t (t + 1) →
      (∃ p ∈ P, wordDist S (vertex X W₁ (t + 1)) p ≤ T) ∨
        (wordDist S (vertex X W₁ t) (vertex X W₁ (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp lam W₂ i' k' →
            (QuotientGroup.mk (vertex X W₂ i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex X W₁ t)))
    {j : ℕ} (hj : j < u.length) :
    (∃ p ∈ P, wordDist S (vertex (vertex X W₁ k) u j) p ≤ 2 * T) ∨
      wordDist S (vertex (vertex X W₁ k) u j) (vertex (vertex X W₁ k) u (j + 1)) ≤ 3 * T + 1 := by
  classical
  have hball4 : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam (C * 4) → wordDist S A B ≤ T :=
    fun lam A B h => hball lam A B (relBall_mono_radius D lam hDc h)
  by_cases hcomp : ∀ (lam : Λ) (e : G), u[j]'hj ≠ RelLetter.comp lam e
  · refine Or.inr ?_
    have h1 := wordDist_vertex_succ_le_one_of_not_comp D hbase (f := vertex X W₁ k) hu.1 hj hcomp
    omega
  push Not at hcomp
  obtain ⟨lam, e, he⟩ := hcomp
  have hc : IsComp lam u j (j + 1) :=
    isComp_succ_of_isCompOf_geodesic D hu hj (by rw [he]; exact rfl)
  have hcosOut : (QuotientGroup.mk (vertex (vertex X W₁ k) u j) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex (vertex X W₁ k) u (j + 1)) :=
    mk_vertex_eq_of_isComp D (vertex X W₁ k) hu.1 hc
  have hA₀ := isGeodesicWord_take D hW₁ hk
  have hB₀ := isGeodesicWord_take D hW₂ hkst
  by_cases hA : AvoidsCosetFrom D lam (QuotientGroup.mk (vertex (vertex X W₁ k) u j)) X (W₁.take k)
  · have hArev := hA.revWord (fun a ha => hW₁.1 a (List.take_subset k _ ha))
    rw [← vertex_eq_mul_listVal_take W₁ X k] at hArev
    have hAgeo := isGeodesicWord_revWord D hsymm hA₀
    by_cases hB : AvoidsCosetFrom D lam
        (QuotientGroup.mk (vertex (vertex X W₁ k) u j)) X (W₂.take kst)
    · -- the letter is isolated in the small triangle
      refine Or.inr ?_
      have h0 := span_mem_relBall_of_noComp D lam hsymm hbnd hDc hu hAgeo hB₀ hc
        (noComp_of_avoidsCosetFrom hArev) (noComp_of_avoidsCosetFrom hB)
      have h1 := hball lam _ _ h0
      omega
    · -- only the second side reaches the coset: its entrance is a partner
      refine Or.inl ?_
      obtain ⟨t, ht, hct, hcost⟩ := exists_of_not_avoidsCosetFrom hB
      have hcB : IsComp lam (W₂.take kst) t (t + 1) :=
        isComp_succ_of_isCompOf_geodesic D hB₀ ht hct
      have hp := isGeodesicWord_revWord D hsymm (isGeodesicWord_take D hu (le_of_lt hj))
      have hap := (avoidsCosetFrom_take_of_isComp D hu hc).revWord
        (fun a ha => hu.1 a (List.take_subset j _ ha))
      rw [← vertex_eq_mul_listVal_take u (vertex X W₁ k) j] at hap
      have hr := isGeodesicWord_take D hB₀ (le_of_lt ht)
      have har := avoidsCosetFrom_take_of_isComp D hB₀ hcB
      rw [hcost] at har
      have h0 := closingJump_located D hsymm hbnd lam hp hAgeo hr hcost hap hArev har
      have h1 := hball4 lam _ _ h0
      have htk : t ≤ kst := by
        have h2 := ht
        simp only [List.length_take] at h2
        omega
      refine ⟨vertex X W₂ t, hP₂ t (by omega), ?_⟩
      rw [wordDist_comm hS, ← vertex_take_eq X W₂ kst t htk]
      omega
  · -- the first side reaches the coset
    obtain ⟨t, ht, hct, hcost⟩ := exists_of_not_avoidsCosetFrom hA
    have htk : t < k := by
      have h2 := ht
      simp only [List.length_take] at h2
      omega
    have hcA : IsComp lam (W₁.take k) t (t + 1) :=
      isComp_succ_of_isCompOf_geodesic D hA₀ ht hct
    have htW : t < W₁.length := by omega
    have hct' : (W₁[t]'htW).IsCompOf lam := by
      rw [List.getElem_take] at hct
      exact hct
    have hcW : IsComp lam W₁ t (t + 1) :=
      isComp_succ_of_isCompOf_geodesic D hW₁ htW hct'
    have hvt : vertex X (W₁.take k) t = vertex X W₁ t := vertex_take_eq X W₁ k t (le_of_lt htk)
    have hvt₁ : vertex X (W₁.take k) (t + 1) = vertex X W₁ (t + 1) :=
      vertex_take_eq X W₁ k (t + 1) htk
    -- the exit of the component and the entrance of the letter are close
    have h0 := exitEntranceConnector_mem_relBall D lam hsymm hbnd hDc hA₀ hu hcA hc hcost
    rw [hvt₁] at h0
    have hd₁ := hball lam _ _ h0
    rcases hside lam t htk hcW with ⟨p, hp, hdp⟩ | ⟨hspan, hno⟩
    · refine Or.inl ⟨p, hp, ?_⟩
      have htri := wordDist_triangle hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1)) p
      rw [wordDist_comm hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))] at htri
      omega
    · -- the component is short and the second side misses the coset: the letter is short
      refine Or.inr ?_
      have hp := geodesicWord_drop D hu (show j + 1 ≤ u.length by omega)
      have hap := avoidsCosetFrom_drop_of_isComp D hu hc
      rw [hcosOut] at hap
      have hq := isGeodesicWord_revWord D hsymm hB₀
      have hK : (QuotientGroup.mk (vertex X W₁ t) : G ⧸ D.fam lam)
          = QuotientGroup.mk (vertex (vertex X W₁ k) u (j + 1)) := by
        rw [← hvt]
        exact hcost.trans hcosOut
      have haq := ((avoidsCosetFrom_of_noComp D hW₂.1 hno).take kst).revWord
        (fun a ha => hW₂.1 a (List.take_subset kst _ ha))
      rw [← vertex_eq_mul_listVal_take W₂ X kst, hK] at haq
      have hr := isGeodesicWord_take D hW₁ (le_of_lt htW)
      have har := avoidsCosetFrom_take_of_isComp D hW₁ hcW
      rw [hK] at har
      have h2 := closingJump_located D hsymm hbnd lam hp hq hr hK hap haq har
      have hd₂ := hball4 lam _ _ h2
      have htri₁ := wordDist_triangle hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))
        (vertex (vertex X W₁ k) u (j + 1))
      have htri₂ := wordDist_triangle hS (vertex X W₁ (t + 1)) (vertex X W₁ t)
        (vertex (vertex X W₁ k) u (j + 1))
      rw [wordDist_comm hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))] at htri₁
      rw [wordDist_comm hS (vertex X W₁ (t + 1)) (vertex X W₁ t)] at htri₂
      omega

/-- **A vertex near a corner is near the other side.** -/
theorem corner_near (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (hbase : ∀ b ∈ D.base, wordNorm S b ≤ 1)
    (hball : ∀ (lam : Λ) (A B : G), A⁻¹ * B ∈ D.relBall lam Dc → wordDist S A B ≤ T)
    (P : Set G) {X Y Z : G} {W₁ W₂ : List (RelLetter G Λ)}
    (hW₁ : IsGeodesicWord D X Y W₁) (hW₂ : IsGeodesicWord D X Z W₂)
    {k kst : ℕ} (hk : k ≤ W₁.length) (hkst : kst ≤ W₂.length)
    {u : List (RelLetter G Λ)}
    (hu : IsGeodesicWord D (vertex X W₁ k) (vertex X W₂ kst) u)
    (hP₂ : ∀ i ≤ W₂.length, vertex X W₂ i ∈ P)
    (hside : ∀ (lam : Λ) (t : ℕ), t < k → IsComp lam W₁ t (t + 1) →
      (∃ p ∈ P, wordDist S (vertex X W₁ (t + 1)) p ≤ T) ∨
        (wordDist S (vertex X W₁ t) (vertex X W₁ (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp lam W₂ i' k' →
            (QuotientGroup.mk (vertex X W₂ i') : G ⧸ D.fam lam)
              ≠ QuotientGroup.mk (vertex X W₁ t))) :
    ∃ p ∈ P, wordDist S (vertex X W₁ k) p ≤ 2 * T + (3 * T + 1) * u.length := by
  have hend : ∃ p ∈ P, wordDist S (vertex (vertex X W₁ k) u u.length) p ≤ 2 * T := by
    refine ⟨vertex X W₂ kst, hP₂ kst hkst, ?_⟩
    rw [hu.vertex_length_eq, wordDist_self]
    omega
  obtain ⟨p, hp, hd⟩ := exists_near_of_walk hS P (fun j => vertex (vertex X W₁ k) u j) u.length
    (2 * T) (3 * T + 1) hend
    (fun j hj => corner_walk_step D hsymm hbnd hDc hS hbase hball P hW₁ hW₂ hk hkst hu hP₂ hside hj)
  refine ⟨p, hp, ?_⟩
  simpa using hd

end Corner

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.wordDist_vertex_succ_le_one_of_not_comp
#audit_axioms GroupApproximation.GGT.HullLemma35.corner_walk_step
#audit_axioms GroupApproximation.GGT.HullLemma35.corner_near
