import GroupApproximation.GGT.HullSCUnconeLemmaB
import GroupApproximation.Algebra.HyperbolicSlimTriangles
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 10: the two other sides of a triangle

For the triangle of chosen geodesic words on `x`, `y`, `z`, `sidePoints J g x y z` is the set of
points of the guessed paths from `x` to `z` and from `z` to `y`.  This module collects what the corner
walk of `GGT/HullSCUnconeLemmaB.lean` needs about it, at both corners `x` and `y` of the side from
`x` to `y`:

* every vertex of the geodesic word from `x` to `z`, from `z` to `y`, and of its reversal, lies in it;
* `exit_near_of_connected`, `entrance_near_of_connected` — the ends of a cyclic component of the side
  from `x` to `y` whose coset another side meets are within `T` of it (Lemma A);
* `side_left`, `side_right` — the side hypothesis of `corner_near` at the corner `x`, and at the
  corner `y` on the reversed words.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

section Geodesic

variable {G : Type u} [Group G] {Λ : Type w}

/-- A vertex of a geodesic word is between its ends. -/
theorem isBetween_vertex_of_isGeodesicWord (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {k : ℕ} (hk : k ≤ w.length) :
    Hyperbolic.IsBetween D.alphabet.carrier f (vertex f w k) g := by
  have h1 := wordDist_vertex_eq_index D hw hk
  have h2 := (geodesicWord_drop D hw hk).2.2
  have h3 := hw.2.2
  rw [List.length_drop] at h2
  show wordDist D.alphabet.carrier f (vertex f w k) + wordDist D.alphabet.carrier (vertex f w k) g
    = wordDist D.alphabet.carrier f g
  omega

/-- A component letter of the reversal of a geodesic word is a component letter of the word. -/
theorem exists_isComp_of_isComp_revWord (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam : Λ} {t : ℕ}
    (hc : IsComp lam (revWord w) t (t + 1)) :
    ∃ t' : ℕ, t' + t + 1 = w.length ∧ IsComp lam w t' (t' + 1) := by
  have hlen : (revWord w).length = w.length := by simp [revWord]
  have hc2 := hc.2.1
  have hm : t < (revWord w).length := by omega
  have hm' : w.length - 1 - t < w.length := by omega
  have hct := (isCompOf_getElem_revWord w lam hm hm').mp (hc.2.2.1 t le_rfl (by omega) hm)
  exact ⟨w.length - 1 - t, by omega, isComp_succ_of_isCompOf_geodesic D hw hm' hct⟩

end Geodesic

section Sides

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **The points of the guessed paths of the other two sides** of the triangle on `x`, `y`, `z`. -/
def sidePoints (J : RelGenSet Q (Sum Lambda I)) (g : I → Q) (x y z : Q) : Set Q :=
  {p | ∃ n ≤ guessLen J g x z, guessPath J g x z n = p} ∪
    {p | ∃ n ≤ guessLen J g z y, guessPath J g z y n = p}

theorem length_expWord_take_le (g : I → Q) (w : List (RelLetter Q (Sum Lambda I))) (k : ℕ) :
    (expWord g (w.take k)).length ≤ (expWord g w).length := by
  rw [expWord_take_append g w k, List.length_append]
  omega

theorem vertex_mem_sidePoints_left (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y z : Q) (i : ℕ) :
    vertex x (geodWord J x z) i ∈ sidePoints J g x y z := by
  rw [← guessPath_at_letter J g hg x z i]
  exact Or.inl ⟨_, length_expWord_take_le g (geodWord J x z) i, rfl⟩

theorem vertex_mem_sidePoints_right (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y z : Q) (i : ℕ) :
    vertex z (geodWord J z y) i ∈ sidePoints J g x y z := by
  rw [← guessPath_at_letter J g hg z y i]
  exact Or.inr ⟨_, length_expWord_take_le g (geodWord J z y) i, rfl⟩

theorem vertex_revWord_mem_sidePoints_right (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y z : Q) {i : ℕ}
    (hi : i ≤ (revWord (geodWord J z y)).length) :
    vertex y (revWord (geodWord J z y)) i ∈ sidePoints J g x y z := by
  have hlen : (revWord (geodWord J z y)).length = (geodWord J z y).length := by simp [revWord]
  have h := vertex_revWord_of_end (geodWord J z y) z ((geodWord J z y).length - i)
  rw [(geodWord_spec J z y).2.1,
    show (geodWord J z y).length - ((geodWord J z y).length - i) = i by omega] at h
  rw [h]
  exact vertex_mem_sidePoints_right J g hg x y z _

/-- **The exit of a connected cyclic component is near the other sides.** -/
theorem exit_near_of_connected (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (x y z : Q) {t : ℕ} (ht : t < (geodWord J x y).length) {i₀ : I} {e : Q}
    (hletter : (geodWord J x y)[t]'ht = RelLetter.comp (Sum.inr i₀) e)
    (hconn : (∃ i₂ k₂ : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t)) ∨
      (∃ i₃ k₃ : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t))) :
    ∃ p ∈ sidePoints J g x y z,
      wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
        (vertex x (geodWord J x y) (t + 1)) p ≤ T := by
  have hpt : guessPath J g x y
      ((expWord g ((geodWord J x y).take t)).length + (expo g i₀ e).natAbs)
        = vertex x (geodWord J x y) (t + 1) := by
    rw [guessPath_letter_point J g hg x y ht hletter le_rfl,
      vertex_succ_eq_mul_zpow J g hg (geodWord_spec J x y).1 ht hletter]
    congr 2
    split_ifs <;> omega
  rcases letter_point_near_sides J g hg hbaseInv hinf hbnd hDc hT x y z ht hletter hconn le_rfl
    with ⟨n, hn, hd⟩ | ⟨n, hn, hd⟩
  · refine ⟨guessPath J g x z n, Or.inl ⟨n, hn, rfl⟩, ?_⟩
    rw [← hpt]
    exact hd
  · refine ⟨guessPath J g z y n, Or.inr ⟨n, hn, rfl⟩, ?_⟩
    rw [← hpt]
    exact hd

/-- **The entrance of a connected cyclic component is near the other sides.** -/
theorem entrance_near_of_connected (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (x y z : Q) {t : ℕ} (ht : t < (geodWord J x y).length) {i₀ : I} {e : Q}
    (hletter : (geodWord J x y)[t]'ht = RelLetter.comp (Sum.inr i₀) e)
    (hconn : (∃ i₂ k₂ : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t)) ∨
      (∃ i₃ k₃ : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t))) :
    ∃ p ∈ sidePoints J g x y z,
      wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
        (vertex x (geodWord J x y) t) p ≤ T := by
  have hpt : guessPath J g x y ((expWord g ((geodWord J x y).take t)).length + 0)
      = vertex x (geodWord J x y) t := by
    rw [add_zero]
    exact guessPath_at_letter J g hg x y t
  rcases letter_point_near_sides J g hg hbaseInv hinf hbnd hDc hT x y z ht hletter hconn
      (Nat.zero_le _) with ⟨n, hn, hd⟩ | ⟨n, hn, hd⟩
  · refine ⟨guessPath J g x z n, Or.inl ⟨n, hn, rfl⟩, ?_⟩
    rw [← hpt]
    exact hd
  · refine ⟨guessPath J g z y n, Or.inr ⟨n, hn, rfl⟩, ?_⟩
    rw [← hpt]
    exact hd

/-- **The side hypothesis of the corner walk at the corner `x`.** -/
theorem side_left (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (x y z : Q) (k : ℕ) :
    ∀ (i₀ : I) (t : ℕ), t < k → IsComp (Sum.inr i₀) (geodWord J x y) t (t + 1) →
      (∃ p ∈ sidePoints J g x y z,
          wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex x (geodWord J x y) (t + 1)) p ≤ T) ∨
        (wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex x (geodWord J x y) t) (vertex x (geodWord J x y) (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i' k' →
            (QuotientGroup.mk (vertex x (geodWord J x z) i') : Q ⧸ J.fam (Sum.inr i₀))
              ≠ QuotientGroup.mk (vertex x (geodWord J x y) t)) := by
  intro i₀ t _ hc
  have hc2 := hc.2.1
  have ht : t < (geodWord J x y).length := by omega
  obtain ⟨e, he⟩ := exists_comp_of_isCompOf (hc.2.2.1 t le_rfl (by omega) ht)
  by_cases hconn : (∃ i₂ k₂ : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t)) ∨
      (∃ i₃ k₃ : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t))
  · exact Or.inl (exit_near_of_connected J g hg hbaseInv hinf hbnd hDc hT x y z ht he hconn)
  · have hno₂ : ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i' k' →
        (QuotientGroup.mk (vertex x (geodWord J x z) i') : Q ⧸ J.fam (Sum.inr i₀))
          ≠ QuotientGroup.mk (vertex x (geodWord J x y) t) :=
      fun i' k' hc' hcos => hconn (Or.inl ⟨i', k', hc', hcos⟩)
    have hno₃ : ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i' k' →
        (QuotientGroup.mk (vertex z (geodWord J z y) i') : Q ⧸ J.fam (Sum.inr i₀))
          ≠ QuotientGroup.mk (vertex x (geodWord J x y) t) :=
      fun i' k' hc' hcos => hconn (Or.inr ⟨i', k', hc', hcos⟩)
    have h0 := span_mem_relBall_of_noComp J (Sum.inr i₀) hbaseInv hbnd hDc (geodWord_spec J x y)
      (geodWord_spec J x z) (geodWord_spec J z y) hc hno₂ hno₃
    exact Or.inr ⟨wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT i₀ h0, hno₂⟩

/-- **The side hypothesis of the corner walk at the corner `y`**, on the reversed words. -/
theorem side_right (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {C Dc T : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : Q) (u : List (RelLetter Q (Sum Lambda I))),
      IsQuasiGeodesicPolygon J 1 0 n v u →
      ∀ (nu : Sum Lambda I) (i k : ℕ), IsComp nu u i k → IsIsolated J.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ J.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc)
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) Dc → (expo g i e).natAbs ≤ T)
    (x y z : Q) (k : ℕ) :
    ∀ (i₀ : I) (t : ℕ), t < k → IsComp (Sum.inr i₀) (revWord (geodWord J x y)) t (t + 1) →
      (∃ p ∈ sidePoints J g x y z,
          wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex y (revWord (geodWord J x y)) (t + 1)) p ≤ T) ∨
        (wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
            (vertex y (revWord (geodWord J x y)) t)
            (vertex y (revWord (geodWord J x y)) (t + 1)) ≤ T ∧
          ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (revWord (geodWord J z y)) i' k' →
            (QuotientGroup.mk (vertex y (revWord (geodWord J z y)) i') : Q ⧸ J.fam (Sum.inr i₀))
              ≠ QuotientGroup.mk (vertex y (revWord (geodWord J x y)) t)) := by
  intro i₀ t _ hc
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hw₁ := geodWord_spec J x y
  have hw₃ := geodWord_spec J z y
  obtain ⟨t', htt, hcW⟩ := exists_isComp_of_isComp_revWord J hw₁ hc
  have hc2 := hcW.2.1
  have ht' : t' < (geodWord J x y).length := by omega
  obtain ⟨e, he⟩ := exists_comp_of_isCompOf (hcW.2.2.1 t' le_rfl (by omega) ht')
  have hv₁ : vertex y (revWord (geodWord J x y)) (t + 1) = vertex x (geodWord J x y) t' := by
    have h := vertex_revWord_of_end (geodWord J x y) x t'
    rwa [hw₁.2.1, show (geodWord J x y).length - t' = t + 1 by omega] at h
  have hv₀ : vertex y (revWord (geodWord J x y)) t = vertex x (geodWord J x y) (t' + 1) := by
    have h := vertex_revWord_of_end (geodWord J x y) x (t' + 1)
    rwa [hw₁.2.1, show (geodWord J x y).length - (t' + 1) = t by omega] at h
  rw [hv₁, hv₀]
  have hcos := mk_vertex_eq_of_isComp J x hw₁.1 hcW
  by_cases hconn : (∃ i₂ k₂ : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i₂ k₂ ∧
        (QuotientGroup.mk (vertex x (geodWord J x z) i₂) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t')) ∨
      (∃ i₃ k₃ : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i₃ k₃ ∧
        (QuotientGroup.mk (vertex z (geodWord J z y) i₃) : Q ⧸ J.fam (Sum.inr i₀))
          = QuotientGroup.mk (vertex x (geodWord J x y) t'))
  · exact Or.inl (entrance_near_of_connected J g hg hbaseInv hinf hbnd hDc hT x y z ht' he hconn)
  · have hno₂ : ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (geodWord J x z) i' k' →
        (QuotientGroup.mk (vertex x (geodWord J x z) i') : Q ⧸ J.fam (Sum.inr i₀))
          ≠ QuotientGroup.mk (vertex x (geodWord J x y) t') :=
      fun i' k' hc' hcos' => hconn (Or.inl ⟨i', k', hc', hcos'⟩)
    have hno₃ : ∀ i' k' : ℕ, IsComp (Sum.inr i₀) (geodWord J z y) i' k' →
        (QuotientGroup.mk (vertex z (geodWord J z y) i') : Q ⧸ J.fam (Sum.inr i₀))
          ≠ QuotientGroup.mk (vertex x (geodWord J x y) t') :=
      fun i' k' hc' hcos' => hconn (Or.inr ⟨i', k', hc', hcos'⟩)
    have h0 := span_mem_relBall_of_noComp J (Sum.inr i₀) hbaseInv hbnd hDc hw₁
      (geodWord_spec J x z) hw₃ hcW hno₂ hno₃
    have hd := wordDist_le_of_mem_relBall_inr J g hg hbaseInv hT i₀ h0
    have hav := (avoidsCosetFrom_of_noComp J hw₃.1 hno₃).revWord hw₃.1
    rw [hw₃.2.1] at hav
    refine Or.inr ⟨?_, ?_⟩
    · rw [wordDist_comm hS]
      exact hd
    · rw [← hcos]
      exact noComp_of_avoidsCosetFrom hav

end Sides

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.isBetween_vertex_of_isGeodesicWord
#audit_axioms GroupApproximation.GGT.Uncone.exists_isComp_of_isComp_revWord
#audit_axioms GroupApproximation.GGT.Uncone.vertex_mem_sidePoints_left
#audit_axioms GroupApproximation.GGT.Uncone.vertex_mem_sidePoints_right
#audit_axioms GroupApproximation.GGT.Uncone.vertex_revWord_mem_sidePoints_right
#audit_axioms GroupApproximation.GGT.Uncone.exit_near_of_connected
#audit_axioms GroupApproximation.GGT.Uncone.entrance_near_of_connected
#audit_axioms GroupApproximation.GGT.Uncone.side_left
#audit_axioms GroupApproximation.GGT.Uncone.side_right
