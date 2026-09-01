import GroupApproximation.GGT.HullYiCyclicProductNonCommensurable
import GroupApproximation.GGT.DGOCorollary612Threshold
import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.HullSCRelatorSeparationBall
import GroupApproximation.GGT.HullSCRelatorWord

/-!
# The finite-family form of DGO Corollary 6.12 used by Hull

The threshold theorem supplies loxodromy.  Pairwise non-commensurability uses
the three-component application of DGO Lemma 4.21(b): the connectors before
and after the middle component are isolated sides of four-edge polygons, hence
uniformly bounded in the relative metric.  Successively choosing powers
outside the resulting finite balls makes a conjugate-power equality
impossible.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## A four-edge connector polygon -/

/-- The connector quadrilateral `x s y⁻¹ r⁻¹`. -/
def yiConnectorQuadWord (lam : Lambda) (x y r s : G) :
    List (RelLetter G Lambda) :=
  [RelLetter.comp lam x, RelLetter.base s,
    RelLetter.comp lam y⁻¹, RelLetter.base r⁻¹]

@[simp] theorem length_yiConnectorQuadWord (lam : Lambda) (x y r s : G) :
    (yiConnectorQuadWord lam x y r s).length = 4 := rfl

theorem listVal_yiConnectorQuadWord {lam : Lambda} {x y r s : G}
    (hclose : x * s = r * y) :
    RelLetter.listVal (yiConnectorQuadWord lam x y r s) = 1 := by
  simp only [yiConnectorQuadWord, RelLetter.listVal, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, RelLetter.val]
  rw [hclose]
  group

theorem isLetter_yiConnectorQuadWord (D : RelGenSet G Lambda) {lam : Lambda}
    {x y r s : G} (hx : x ∈ D.fam lam) (hy : y ∈ D.fam lam)
    (hr : r ∈ D.base) (hs : s ∈ D.base)
    (hrinv : r⁻¹ ∈ D.base) :
    ∀ c ∈ yiConnectorQuadWord lam x y r s, D.IsLetter c := by
  intro c hc
  have hc4 : c = RelLetter.comp lam x ∨ c = RelLetter.base s ∨
      c = RelLetter.comp lam y⁻¹ ∨ c = RelLetter.base r⁻¹ := by
    simpa [yiConnectorQuadWord] using hc
  rcases hc4 with rfl | rfl | rfl | rfl
  · exact hx
  · exact hs
  · exact inv_mem hy
  · exact hrinv

/-- Four nontrivial admissible letters forming a cycle give a geodesic
four-gon with the identity cut. -/
theorem isQuasiGeodesicPolygon_yiConnectorQuadWord
    (D : RelGenSet G Lambda) {lam : Lambda} {x y r s : G}
    (hx : x ∈ D.fam lam) (hy : y ∈ D.fam lam)
    (hr : r ∈ D.base) (hs : s ∈ D.base) (hrinv : r⁻¹ ∈ D.base)
    (hclose : x * s = r * y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    IsQuasiGeodesicPolygon D 1 0 4 1
      (yiConnectorQuadWord lam x y r s) := by
  let q := yiConnectorQuadWord lam x y r s
  have hlen : q.length = 4 := by simp [q]
  have hval : ∀ j : ℕ, ∀ hj : j < q.length, (q[j]'hj).val ≠ 1 := by
    intro j hj
    have hj4 : j < 4 := by omega
    interval_cases j
    · exact hx1
    · exact hs1
    · exact inv_ne_one.mpr hy1
    · exact inv_ne_one.mpr hr1
  refine ⟨isLetter_yiConnectorQuadWord D hx hy hr hs hrinv,
    listVal_yiConnectorQuadWord hclose, fun t ↦ t, rfl, hlen.symm,
    fun t ↦ Nat.le_succ t, ?_⟩
  intro t _ p q' hp hpq hq'
  rw [div_one, sub_zero]
  have key : q' - p ≤ wordDist D.alphabet.carrier
      (vertex (1 : G) q p) (vertex (1 : G) q q') := by
    rcases Nat.eq_or_lt_of_le hpq with heq | hlt
    · rw [heq, Nat.sub_self]
      exact Nat.zero_le _
    · have hq1 : q' = p + 1 := by omega
      subst hq1
      have hpw : p < q.length := by omega
      have hstep := one_le_wordDist_vertex_succ D 1 q p hpw (hval p hpw)
      omega
  exact_mod_cast key

theorem isComp_yiConnectorQuadWord_zero {lam : Lambda} (x y r s : G) :
    IsComp lam (yiConnectorQuadWord lam x y r s) 0 1 := by
  refine ⟨by omega, by simp, ?_, ?_, ?_⟩
  · intro j _ hj _
    have : j = 0 := by omega
    subst j
    rfl
  · intro j hj
    omega
  · intro _ hc
    exact hc

theorem isComp_yiConnectorQuadWord_two {lam : Lambda} (x y r s : G) :
    IsComp lam (yiConnectorQuadWord lam x y r s) 2 3 := by
  refine ⟨by omega, by simp, ?_, ?_, ?_⟩
  · intro j hj2 hj3 _
    have : j = 2 := by omega
    subst j
    rfl
  · intro j hj _ hc
    have : j = 1 := by omega
    subst j
    exact hc
  · intro _ hc
    exact hc

/-- The two connector components are isolated because the intervening base
letter `s` is outside the peripheral subgroup. -/
theorem isIsolated_yiConnectorQuadWord_zero_two
    (D : RelGenSet G Lambda) {lam : Lambda} {x y r s : G}
    (hx : x ∈ D.fam lam) (hsnot : s ∉ D.fam lam) :
    IsIsolated D.fam lam 1 (yiConnectorQuadWord lam x y r s) 0 ∧
      IsIsolated D.fam lam 1 (yiConnectorQuadWord lam x y r s) 2 := by
  have hnotConnected : ¬ Connected D.fam lam 1
      (yiConnectorQuadWord lam x y r s) 0 2 := by
    intro hc
    have hc' : x * s ∈ D.fam lam := by
      simpa [Connected, yiConnectorQuadWord] using hc
    apply hsnot
    have hm := mul_mem (inv_mem hx) hc'
    simpa only [inv_mul_cancel_left] using hm
  have hstarts : ∀ j : ℕ,
      IsCompStart lam (yiConnectorQuadWord lam x y r s) j → j = 0 ∨ j = 2 := by
    rintro j ⟨k, hj⟩
    have hj4 : j < 4 := by
      have := hj.1
      have := hj.2.1
      omega
    have hletter := hj.2.2.1 j le_rfl hj.1 (by simp; omega)
    interval_cases j
    · exact Or.inl rfl
    · exact False.elim hletter
    · exact Or.inr rfl
    · exact False.elim hletter
  constructor
  · refine ⟨⟨1, isComp_yiConnectorQuadWord_zero x y r s⟩, ?_⟩
    intro j hj hstart
    rcases hstarts j hstart with rfl | rfl
    · exact (hj rfl).elim
    · exact hnotConnected
  · refine ⟨⟨3, isComp_yiConnectorQuadWord_two x y r s⟩, ?_⟩
    intro j hj hstart
    rcases hstarts j hstart with rfl | rfl
    · exact fun hc ↦ hnotConnected (connected_symm hc)
    · exact (hj rfl).elim

/-- Both endpoint connectors of a two-component rectangle lie in one fixed
relative ball.  Trivial connectors are handled by the radius-two base word;
otherwise Proposition 4.14 applies to the isolated sides of the four-gon. -/
theorem exists_radius_connectors_of_base_rectangle
    (D : RelGenSet G Lambda) (hbase : IsSymmetricGeneratingSet D.base)
    {delta : ℕ} (hdelta : Hyperbolic.IsFourPointHyperbolic
      D.alphabet.carrier delta) :
    ∃ R : ℕ, ∀ (lam : Lambda) (x y r s : G),
      x ∈ D.fam lam → y ∈ D.fam lam →
      r ∈ D.base → s ∈ D.base → r ∉ D.fam lam →
      s ∉ D.fam lam → x * s = r * y →
      x ∈ D.relBall lam R ∧ y ∈ D.relBall lam R := by
  obtain ⟨R0, hR0⟩ := exists_isolatedComponentBound_nGon D
    hbase.inv_mem 0 hdelta 4
  refine ⟨max R0 2, ?_⟩
  intro lam x y r s hx hy hr hs hrnot hsnot hclose
  have hrinv := hbase.inv_mem r hr
  have hs1 : s ≠ 1 := fun hs1 ↦ hsnot (by simpa [hs1] using one_mem (D.fam lam))
  have hr1 : r ≠ 1 := fun hr1 ↦ hrnot (by simpa [hr1] using one_mem (D.fam lam))
  rcases eq_or_ne x 1 with rfl | hx1
  · have hyEq : y = r⁻¹ * s := by
      calc
        y = r⁻¹ * (r * y) := by group
        _ = r⁻¹ * (1 * s) := by rw [← hclose]
        _ = r⁻¹ * s := by group
    have hyr : y ∈ D.relBall lam 2 := by
      apply mem_relBall_of_wordNorm_le hbase hy
      rw [hyEq]
      have hmul := wordNorm_mul_le hbase r⁻¹ s
      have hrn : wordNorm D.base r⁻¹ ≤ 1 :=
        wordNorm_le_one_of_mem hrinv
      have hsn : wordNorm D.base s ≤ 1 := wordNorm_le_one_of_mem hs
      omega
    exact ⟨one_mem_relBall D lam _,
      relBall_mono_radius D lam (le_max_right _ _) hyr⟩
  · rcases eq_or_ne y 1 with rfl | hy1
    · have hxEq : x = r * s⁻¹ := by
        calc
          x = (x * s) * s⁻¹ := by group
          _ = (r * 1) * s⁻¹ := by rw [hclose]
          _ = r * s⁻¹ := by group
      have hxr : x ∈ D.relBall lam 2 := by
        apply mem_relBall_of_wordNorm_le hbase hx
        rw [hxEq]
        have hmul := wordNorm_mul_le hbase r s⁻¹
        have hrn : wordNorm D.base r ≤ 1 := wordNorm_le_one_of_mem hr
        have hsn : wordNorm D.base s⁻¹ ≤ 1 :=
          wordNorm_le_one_of_mem (hbase.inv_mem s hs)
        omega
      exact ⟨relBall_mono_radius D lam (le_max_right _ _) hxr,
        one_mem_relBall D lam _⟩
    · have hpoly := isQuasiGeodesicPolygon_yiConnectorQuadWord D
        hx hy hr hs hrinv hclose hx1 hy1 hr1 hs1
      obtain ⟨hiso0, hiso2⟩ :=
        isIsolated_yiConnectorQuadWord_zero_two D hx hsnot
      have hxR := hR0 1 (yiConnectorQuadWord lam x y r s) hpoly lam 0 1
        (isComp_yiConnectorQuadWord_zero x y r s) hiso0
      have hyInvR := hR0 1 (yiConnectorQuadWord lam x y r s) hpoly lam 2 3
        (isComp_yiConnectorQuadWord_two x y r s) hiso2
      have hxSpan : (vertex (1 : G) (yiConnectorQuadWord lam x y r s) 0)⁻¹ *
          vertex (1 : G) (yiConnectorQuadWord lam x y r s) 1 = x := by
        simp [yiConnectorQuadWord]
      have hySpan : (vertex (1 : G) (yiConnectorQuadWord lam x y r s) 2)⁻¹ *
          vertex (1 : G) (yiConnectorQuadWord lam x y r s) 3 = y⁻¹ := by
        simp [yiConnectorQuadWord]
        group
      rw [hxSpan] at hxR
      rw [hySpan] at hyInvR
      have hyR := relBall_inv D lam hbase.inv_mem hyInvR
      rw [inv_inv] at hyR
      exact ⟨relBall_mono_radius D lam (le_max_left _ _) hxR,
        relBall_mono_radius D lam (le_max_left _ _) hyR⟩

/-! ## Successively separated powers -/

/-- A finite family of infinite-order elements admits one common exponent
whose positive and negative powers avoid a prescribed finite set. -/
theorem exists_deep_pow_finite_family {I : Type*} [Fintype I]
    (a : I → G) (hinj : ∀ i, Function.Injective (fun n : ℕ ↦ a i ^ n))
    {S : Set G} (hS : S.Finite) (n0 : ℕ) :
    ∃ m : ℕ, n0 ≤ m ∧ ∀ i, a i ^ m ∉ S ∧ (a i ^ m)⁻¹ ∉ S := by
  classical
  have hS' : (S ∪ (fun x : G ↦ x⁻¹) '' S).Finite := hS.union (hS.image _)
  have hpre : ∀ i : I,
      ((fun n : ℕ ↦ a i ^ n) ⁻¹' (S ∪ (fun x : G ↦ x⁻¹) '' S)).Finite :=
    fun i ↦ Set.Finite.preimage (fun _ _ _ _ hxy ↦ hinj i hxy) hS'
  choose bound hbound using fun i : I ↦ (hpre i).bddAbove
  let B := Finset.univ.sup bound
  let m := max n0 (B + 1)
  refine ⟨m, le_max_left _ _, ?_⟩
  intro i
  have hlarge : B < m := by
    exact lt_of_lt_of_le (Nat.lt_succ_self B) (le_max_right _ _)
  have houtside : a i ^ m ∉ S ∪ (fun x : G ↦ x⁻¹) '' S := by
    intro hm
    have hmle : m ≤ bound i := hbound i hm
    have hile : bound i ≤ B := Finset.le_sup (f := bound) (Finset.mem_univ i)
    omega
  exact ⟨fun hm ↦ houtside (Or.inl hm),
    fun hm ↦ houtside (Or.inr ⟨(a i ^ m)⁻¹, hm, inv_inv _⟩)⟩

/-- Powers may be chosen in order so that each new positive and negative
power lies beyond the depth of every earlier one. -/
theorem exists_successivelySeparatedPowers
    (D : RelGenSet G Lambda) (lam : Lambda) (hbase : IsSymmetricGeneratingSet D.base)
    (hloc : ∀ n, (D.relBall lam n).Finite) {h : G}
    (hinj : Function.Injective (fun n : ℕ ↦ h ^ n)) (C R N : ℕ) :
    ∃ a : Fin N → G,
      (∀ j, ∃ m : ℕ, 0 < m ∧ a j = h ^ m) ∧
      (∀ j, a j ∉ D.relBall lam C ∧ (a j)⁻¹ ∉ D.relBall lam C) ∧
      ∀ i j, i < j →
        a j ∉ D.relBall lam (wordNorm D.base (a i) + 2 * R) ∧
        (a j)⁻¹ ∉ D.relBall lam (wordNorm D.base (a i) + 2 * R) := by
  classical
  induction N with
  | zero =>
      exact ⟨Fin.elim0, fun j ↦ Fin.elim0 j,
        fun j ↦ Fin.elim0 j, fun i ↦ Fin.elim0 i⟩
  | succ N ih =>
      obtain ⟨old, holdPow, holdDeep, holdSep⟩ := ih
      let depth := max C
        (Finset.univ.sup (fun i : Fin N ↦ wordNorm D.base (old i) + 2 * R))
      obtain ⟨m, hm, hmDeep, hmInvDeep⟩ :=
        exists_deep_pow hinj (hloc depth) 1
      let fresh := h ^ m
      let a : Fin (N + 1) → G := Fin.snoc old fresh
      refine ⟨a, ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · exact ⟨m, hm, by simp [a, fresh, Fin.snoc_last]⟩
        · intro i
          obtain ⟨q, hq, hold⟩ := holdPow i
          exact ⟨q, hq, by simpa [a, Fin.snoc_castSucc] using hold⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · constructor
          · exact fun hc ↦ hmDeep (relBall_mono_radius D lam
              (le_trans (le_max_left _ _) le_rfl) hc)
          · exact fun hc ↦ hmInvDeep (relBall_mono_radius D lam
              (le_trans (le_max_left _ _) le_rfl) hc)
        · intro i
          simpa [a, Fin.snoc_castSucc] using holdDeep i
      · intro i j hij
        refine Fin.lastCases ?_ ?_ j
        · have hi : i ≠ Fin.last N := by omega
          let i0 : Fin N := ⟨i.val, by
            have hilast : i < Fin.last N := lt_of_le_of_ne (Fin.le_last i) hi
            simpa using hilast⟩
          have hi0 : i0.castSucc = i := Fin.ext rfl
          rw [← hi0]
          have hile : wordNorm D.base (old i0) + 2 * R ≤ depth := by
            exact le_trans (Finset.le_sup (f := fun q : Fin N ↦
              wordNorm D.base (old q) + 2 * R) (Finset.mem_univ i0))
              (le_max_right _ _)
          constructor
          · intro hf
            apply hmDeep
            exact relBall_mono_radius D lam hile (by simpa [a, fresh] using hf)
          · intro hf
            apply hmInvDeep
            exact relBall_mono_radius D lam hile (by simpa [a, fresh] using hf)
        · intro j0
          let i0 : Fin N := ⟨i.val, by
            have hilast : i.val < N := lt_of_lt_of_le hij j0.isLt
            exact hilast⟩
          have hi0 : i0.castSucc = i := Fin.ext rfl
          rw [← hi0] at hij ⊢
          have hij0 : i0 < j0 := hij
          simpa [a, Fin.snoc_castSucc] using holdSep i0 j0 hij0

end HullSC
end GroupApproximation
