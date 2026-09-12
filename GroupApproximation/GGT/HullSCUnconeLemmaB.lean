import GroupApproximation.GGT.HullSCUnconeWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 9: a vertex near a corner is near the other side

Let `W₁` and `W₂` be geodesic words of `J` from a corner `X`, let `p₀` be the `k`-th vertex of `W₁`,
`q*` the `k*`-th vertex of `W₂`, and `u` a geodesic word from `p₀` to `q*`.  Suppose every vertex of
`W₂` lies in a set `P`, and every cyclic letter of `W₁` before `p₀` either has its exit within `T` of
`P`, or is short in the un-coned metric while `W₂` misses its coset.  Then `p₀` is within
`2T + (3T + 1)|u|` of `P` in the un-coned metric (`corner_near`).

The proof walks along `u` (`exists_near_of_walk`).  At a letter of a cyclic member on a coset `K`
(`corner_walk_step`):

* if neither `W₁` before `p₀` nor `W₂` before `q*` meets `K`, the letter is isolated in the small
  triangle and short;
* if only `W₂` meets `K`, the closing jump of a quadrilateral puts the entrance of `W₂` into `K`
  within `T` of the walk;
* if `W₁` meets `K`, its exit is close to the entrance of the letter; then either that exit is near
  `P`, or the component is short, `W₂` misses `K`, and a second closing jump makes the letter short.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

section Avoid

variable {G : Type u} [Group G] {Λ : Type w}

/-- A word avoiding a coset has no component on it. -/
theorem noComp_of_avoidsCosetFrom {D : RelGenSet G Λ} {lam : Λ} {K : G ⧸ D.fam lam} {f : G}
    {u : List (RelLetter G Λ)} (h : AvoidsCosetFrom D lam K f u) :
    ∀ i k : ℕ, IsComp lam u i k → (QuotientGroup.mk (vertex f u i) : G ⧸ D.fam lam) ≠ K := by
  intro i k hc
  have hi : i < u.length := by
    have := hc.1
    have := hc.2.1
    omega
  exact h i hi (hc.2.2.1 i le_rfl hc.1 hi)

/-- A word not avoiding a coset has a component letter on it. -/
theorem exists_of_not_avoidsCosetFrom {D : RelGenSet G Λ} {lam : Λ} {K : G ⧸ D.fam lam} {f : G}
    {u : List (RelLetter G Λ)} (h : ¬ AvoidsCosetFrom D lam K f u) :
    ∃ (t : ℕ) (ht : t < u.length), (u[t]'ht).IsCompOf lam ∧
      (QuotientGroup.mk (vertex f u t) : G ⧸ D.fam lam) = K := by
  by_contra hne
  exact h fun t ht hct hcos => hne ⟨t, ht, hct, hcos⟩

end Avoid

section Corner

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **One step of the walk from a corner vertex toward the other side.** -/
theorem corner_walk_step (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (P : Set Q) {X Y Z : Q} {W₁ W₂ : List (RelLetter Q (Sum Lambda I))}
    (hW₁ : IsGeodesicWord J X Y W₁) (hW₂ : IsGeodesicWord J X Z W₂)
    {k kst : ℕ} (hk : k ≤ W₁.length) (hkst : kst ≤ W₂.length)
    {u : List (RelLetter Q (Sum Lambda I))}
    (hu : IsGeodesicWord J (vertex X W₁ k) (vertex X W₂ kst) u)
    (hP₂ : ∀ i ≤ W₂.length, vertex X W₂ i ∈ P)
    (hside : ∀ (i₀ : I) (t : ℕ), t < k → IsComp (Sum.inr i₀) W₁ t (t + 1) →
      (∃ p ∈ P, wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
          (vertex X W₁ (t + 1)) p ≤ T) ∨
        (wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex X W₁ t) (vertex X W₁ (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp (Sum.inr i₀) W₂ i' k' →
            (QuotientGroup.mk (vertex X W₂ i') : Q ⧸ J.fam (Sum.inr i₀))
              ≠ QuotientGroup.mk (vertex X W₁ t)))
    {j : ℕ} (hj : j < u.length) :
    (∃ p ∈ P, wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
        (vertex (vertex X W₁ k) u j) p ≤ 2 * T) ∨
      wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
        (vertex (vertex X W₁ k) u j) (vertex (vertex X W₁ k) u (j + 1)) ≤ 3 * T + 1 := by
  classical
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hT4 : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) (C * 4) → (expo g i e).natAbs ≤ T :=
    fun i e he => hT i e (relBall_mono_radius J (Sum.inr i) hDc he)
  by_cases hinr : ∀ (i₀ : I) (e : Q), u[j]'hj ≠ RelLetter.comp (Sum.inr i₀) e
  · refine Or.inr ?_
    have h1 := wordDist_vertex_succ_le_one_of_not_inr J g hg hbaseInv (f := vertex X W₁ k) hu.1
      hj hinr
    omega
  push Not at hinr
  obtain ⟨i₀, e, he⟩ := hinr
  have hc : IsComp (Sum.inr i₀) u j (j + 1) :=
    isComp_succ_of_isCompOf_geodesic J hu hj (by rw [he]; exact rfl)
  have hcosOut : (QuotientGroup.mk (vertex (vertex X W₁ k) u j) : Q ⧸ J.fam (Sum.inr i₀))
      = QuotientGroup.mk (vertex (vertex X W₁ k) u (j + 1)) :=
    mk_vertex_eq_of_isComp J (vertex X W₁ k) hu.1 hc
  have hA₀ := isGeodesicWord_take J hW₁ hk
  have hB₀ := isGeodesicWord_take J hW₂ hkst
  by_cases hA : AvoidsCosetFrom J (Sum.inr i₀)
      (QuotientGroup.mk (vertex (vertex X W₁ k) u j)) X (W₁.take k)
  · have hArev := hA.revWord (fun a ha => hW₁.1 a (List.take_subset k _ ha))
    rw [← vertex_eq_mul_listVal_take W₁ X k] at hArev
    have hAgeo := isGeodesicWord_revWord J hbaseInv hA₀
    by_cases hB : AvoidsCosetFrom J (Sum.inr i₀)
        (QuotientGroup.mk (vertex (vertex X W₁ k) u j)) X (W₂.take kst)
    · -- the letter is isolated in the small triangle
      refine Or.inr ?_
      have h0 := span_mem_relBall_of_noComp J (Sum.inr i₀) hbaseInv hbnd hDc hu hAgeo hB₀ hc
        (noComp_of_avoidsCosetFrom hArev) (noComp_of_avoidsCosetFrom hB)
      have h1 := wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT i₀ h0
      omega
    · -- only the second side reaches the coset: its entrance is a partner
      refine Or.inl ?_
      obtain ⟨t, ht, hct, hcost⟩ := exists_of_not_avoidsCosetFrom hB
      have hcB : IsComp (Sum.inr i₀) (W₂.take kst) t (t + 1) :=
        isComp_succ_of_isCompOf_geodesic J hB₀ ht hct
      have hp := isGeodesicWord_revWord J hbaseInv (isGeodesicWord_take J hu (le_of_lt hj))
      have hap := (avoidsCosetFrom_take_of_isComp J hu hc).revWord
        (fun a ha => hu.1 a (List.take_subset j _ ha))
      rw [← vertex_eq_mul_listVal_take u (vertex X W₁ k) j] at hap
      have hr := isGeodesicWord_take J hB₀ (le_of_lt ht)
      have har := avoidsCosetFrom_take_of_isComp J hB₀ hcB
      rw [hcost] at har
      have h0 := closingJump_located J hbaseInv hbnd (Sum.inr i₀) hp hAgeo hr hcost hap hArev har
      have h1 := wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT4 i₀ h0
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
    have hcA : IsComp (Sum.inr i₀) (W₁.take k) t (t + 1) :=
      isComp_succ_of_isCompOf_geodesic J hA₀ ht hct
    have htW : t < W₁.length := by omega
    have hct' : (W₁[t]'htW).IsCompOf (Sum.inr i₀) := by
      rw [List.getElem_take] at hct
      exact hct
    have hcW : IsComp (Sum.inr i₀) W₁ t (t + 1) :=
      isComp_succ_of_isCompOf_geodesic J hW₁ htW hct'
    have hvt : vertex X (W₁.take k) t = vertex X W₁ t := vertex_take_eq X W₁ k t (le_of_lt htk)
    have hvt₁ : vertex X (W₁.take k) (t + 1) = vertex X W₁ (t + 1) :=
      vertex_take_eq X W₁ k (t + 1) htk
    -- the exit of the component and the entrance of the letter are close
    have h0 := exitEntranceConnector_mem_relBall J (Sum.inr i₀) hbaseInv hbnd hDc hA₀ hu hcA hc
      hcost
    rw [hvt₁] at h0
    have hd₁ := wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT i₀ h0
    rcases hside i₀ t htk hcW with ⟨p, hp, hdp⟩ | ⟨hspan, hno⟩
    · refine Or.inl ⟨p, hp, ?_⟩
      have htri := wordDist_triangle hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1)) p
      rw [wordDist_comm hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))] at htri
      omega
    · -- the component is short and the second side misses the coset: the letter is short
      refine Or.inr ?_
      have hp := geodesicWord_drop J hu (show j + 1 ≤ u.length by omega)
      have hap := avoidsCosetFrom_drop_of_isComp J hu hc
      rw [hcosOut] at hap
      have hq := isGeodesicWord_revWord J hbaseInv hB₀
      have hK : (QuotientGroup.mk (vertex X W₁ t) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex (vertex X W₁ k) u (j + 1)) := by
        rw [← hvt]
        exact hcost.trans hcosOut
      have haq := ((avoidsCosetFrom_of_noComp J hW₂.1 hno).take kst).revWord
        (fun a ha => hW₂.1 a (List.take_subset kst _ ha))
      rw [← vertex_eq_mul_listVal_take W₂ X kst, hK] at haq
      have hr := isGeodesicWord_take J hW₁ (le_of_lt htW)
      have har := avoidsCosetFrom_take_of_isComp J hW₁ hcW
      rw [hK] at har
      have h2 := closingJump_located J hbaseInv hbnd (Sum.inr i₀) hp hq hr hK hap haq har
      have hd₂ := wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT4 i₀ h2
      have htri₁ := wordDist_triangle hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))
        (vertex (vertex X W₁ k) u (j + 1))
      have htri₂ := wordDist_triangle hS (vertex X W₁ (t + 1)) (vertex X W₁ t)
        (vertex (vertex X W₁ k) u (j + 1))
      rw [wordDist_comm hS (vertex (vertex X W₁ k) u j) (vertex X W₁ (t + 1))] at htri₁
      rw [wordDist_comm hS (vertex X W₁ (t + 1)) (vertex X W₁ t)] at htri₂
      omega

/-- **A vertex near a corner is near the other side.** -/
theorem corner_near (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (P : Set Q) {X Y Z : Q} {W₁ W₂ : List (RelLetter Q (Sum Lambda I))}
    (hW₁ : IsGeodesicWord J X Y W₁) (hW₂ : IsGeodesicWord J X Z W₂)
    {k kst : ℕ} (hk : k ≤ W₁.length) (hkst : kst ≤ W₂.length)
    {u : List (RelLetter Q (Sum Lambda I))}
    (hu : IsGeodesicWord J (vertex X W₁ k) (vertex X W₂ kst) u)
    (hP₂ : ∀ i ≤ W₂.length, vertex X W₂ i ∈ P)
    (hside : ∀ (i₀ : I) (t : ℕ), t < k → IsComp (Sum.inr i₀) W₁ t (t + 1) →
      (∃ p ∈ P, wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
          (vertex X W₁ (t + 1)) p ≤ T) ∨
        (wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex X W₁ t) (vertex X W₁ (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp (Sum.inr i₀) W₂ i' k' →
            (QuotientGroup.mk (vertex X W₂ i') : Q ⧸ J.fam (Sum.inr i₀))
              ≠ QuotientGroup.mk (vertex X W₁ t))) :
    ∃ p ∈ P, wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (vertex X W₁ k) p ≤ 2 * T + (3 * T + 1) * u.length := by
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hend : ∃ p ∈ P, wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (vertex (vertex X W₁ k) u u.length) p ≤ 2 * T := by
    refine ⟨vertex X W₂ kst, hP₂ kst hkst, ?_⟩
    rw [hu.vertex_length_eq, wordDist_self]
    omega
  obtain ⟨p, hp, hd⟩ := exists_near_of_walk hS P (fun j => vertex (vertex X W₁ k) u j) u.length
    (2 * T) (3 * T + 1) hend
    (fun j hj => corner_walk_step J g hg hbaseInv hbnd hDc hT P hW₁ hW₂ hk hkst hu hP₂ hside hj)
  refine ⟨p, hp, ?_⟩
  simpa using hd

end Corner

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.noComp_of_avoidsCosetFrom
#audit_axioms GroupApproximation.GGT.Uncone.exists_of_not_avoidsCosetFrom
#audit_axioms GroupApproximation.GGT.Uncone.corner_walk_step
#audit_axioms GroupApproximation.GGT.Uncone.corner_near
