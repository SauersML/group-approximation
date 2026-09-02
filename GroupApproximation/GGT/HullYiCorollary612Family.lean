import GroupApproximation.GGT.HullYiCyclicProductNonCommensurable
import GroupApproximation.GGT.DGOCorollary612Threshold
import GroupApproximation.GGT.DGOCorollary427Full
import GroupApproximation.GGT.DGOIsolatedComponentCut
import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.DGOWWordConditions
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
  calc
    x * (s * (y⁻¹ * (r⁻¹ * 1))) = (x * s) * y⁻¹ * r⁻¹ := by group
    _ = (r * y) * y⁻¹ * r⁻¹ := by rw [hclose]
    _ = 1 := by group

theorem isLetter_yiConnectorQuadWord (D : RelGenSet G Lambda) {lam : Lambda}
    {x y r s : G} (hx : x ∈ D.fam lam) (hy : y ∈ D.fam lam)
    (_hr : r ∈ D.base) (hs : s ∈ D.base)
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
    IsQuasiGeodesicPolygon D 1 ((0 : ℕ) : ℝ) 4 1
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
  have hp' : t ≤ p := hp
  have hq'' : q' ≤ t + 1 := hq'
  simp only [div_one, Nat.cast_zero, sub_zero]
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
      simpa [Connected, yiConnectorQuadWord, RelLetter.val] using hc
    apply hsnot
    have hm := mul_mem (inv_mem hx) hc'
    simpa only [inv_mul_cancel_left] using hm
  have hstarts : ∀ j : ℕ,
      IsCompStart lam (yiConnectorQuadWord lam x y r s) j → j = 0 ∨ j = 2 := by
    rintro j ⟨k, hj⟩
    have hj4 : j < (yiConnectorQuadWord lam x y r s).length :=
      lt_of_lt_of_le hj.1 hj.2.1
    have hletter := hj.2.2.1 j le_rfl hj.1 hj4
    rw [length_yiConnectorQuadWord] at hj4
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
  have hs1 : s ≠ 1 := by
    intro hsEq
    subst s
    exact hsnot (one_mem (D.fam lam))
  have hr1 : r ≠ 1 := by
    intro hrEq
    subst r
    exact hrnot (one_mem (D.fam lam))
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
    · have hpoly : IsQuasiGeodesicPolygon D 1 ((0 : ℕ) : ℝ) 4 1
          (yiConnectorQuadWord lam x y r s) :=
        isQuasiGeodesicPolygon_yiConnectorQuadWord D
          hx hy hr hs hrinv hclose hx1 hy1 hr1 hs1
      obtain ⟨hiso0, hiso2⟩ :=
        isIsolated_yiConnectorQuadWord_zero_two D hx hsnot
      have hxR := hR0 1 (yiConnectorQuadWord lam x y r s) hpoly lam 0 1
        (isComp_yiConnectorQuadWord_zero x y r s) hiso0
      have hyInvR := hR0 1 (yiConnectorQuadWord lam x y r s) hpoly lam 2 3
        (isComp_yiConnectorQuadWord_two x y r s) hiso2
      have hxSpan : (vertex (1 : G) (yiConnectorQuadWord lam x y r s) 0)⁻¹ *
          vertex (1 : G) (yiConnectorQuadWord lam x y r s) 1 = x := by
        simp [yiConnectorQuadWord, RelLetter.val]
      have hySpan : (vertex (1 : G) (yiConnectorQuadWord lam x y r s) 2)⁻¹ *
          vertex (1 : G) (yiConnectorQuadWord lam x y r s) 3 = y⁻¹ := by
        simp [yiConnectorQuadWord, RelLetter.val]
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
    (D : RelGenSet G Lambda) (lam : Lambda)
    (_hbase : IsSymmetricGeneratingSet D.base)
    (hloc : ∀ n, (D.relBall lam n).Finite) {h : G}
    (hinj : Function.Injective (fun n : ℕ ↦ h ^ n))
    (extra : Set G) (hextra : extra.Finite) (C R N : ℕ) :
    ∃ a : Fin N → G,
      (∀ j, ∃ m : ℕ, 0 < m ∧ a j = h ^ m) ∧
      (∀ j, a j ∉ D.relBall lam C ∧ (a j)⁻¹ ∉ D.relBall lam C) ∧
      (∀ j, a j ∉ extra ∧ (a j)⁻¹ ∉ extra) ∧
      ∀ i j, i < j →
        a j ∉ D.relBall lam (wordNorm D.base (a i) + 2 * R) ∧
        (a j)⁻¹ ∉ D.relBall lam (wordNorm D.base (a i) + 2 * R) := by
  classical
  induction N with
  | zero =>
      exact ⟨Fin.elim0, fun j ↦ Fin.elim0 j,
        fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j, fun i ↦ Fin.elim0 i⟩
  | succ N ih =>
      obtain ⟨old, holdPow, holdDeep, holdExtra, holdSep⟩ := ih
      let depth := max C
        (Finset.univ.sup (fun i : Fin N ↦ wordNorm D.base (old i) + 2 * R))
      obtain ⟨m, hm, hmDeep, hmInvDeep⟩ :=
        exists_deep_pow hinj ((hloc depth).union hextra) 1
      let fresh := h ^ m
      let a : Fin (N + 1) → G := Fin.snoc old fresh
      refine ⟨a, ?_, ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · exact ⟨m, hm, by simp [a, fresh, Fin.snoc_last]⟩
        · intro i
          obtain ⟨q, hq, hold⟩ := holdPow i
          exact ⟨q, hq, by simpa [a, Fin.snoc_castSucc] using hold⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · constructor
          · intro hc
            have hlast : a (Fin.last N) = h ^ m := by
              simp [a, fresh, Fin.snoc_last]
            rw [hlast] at hc
            exact hmDeep (Or.inl (relBall_mono_radius D lam
              (le_max_left _ _) hc))
          · intro hc
            have hlast : (a (Fin.last N))⁻¹ = (h ^ m)⁻¹ := by
              simp [a, fresh, Fin.snoc_last]
            rw [hlast] at hc
            exact hmInvDeep (Or.inl (relBall_mono_radius D lam
              (le_max_left _ _) hc))
        · intro i
          simpa [a, Fin.snoc_castSucc] using holdDeep i
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · constructor
          · intro hc
            have hlast : a (Fin.last N) = h ^ m := by
              simp [a, fresh, Fin.snoc_last]
            rw [hlast] at hc
            exact hmDeep (Or.inr hc)
          · intro hc
            have hlast : (a (Fin.last N))⁻¹ = (h ^ m)⁻¹ := by
              simp [a, fresh, Fin.snoc_last]
            rw [hlast] at hc
            exact hmInvDeep (Or.inr hc)
        · intro i
          simpa [a, Fin.snoc_castSucc] using holdExtra i
      · intro i j
        refine Fin.lastCases ?_ ?_ j
        · intro hij
          let i0 : Fin N := ⟨i.val, by
            have hilast : i < Fin.last N := hij
            change i.val < N at hilast
            exact hilast⟩
          have hi0 : i0.castSucc = i := Fin.ext rfl
          rw [← hi0]
          have hile : wordNorm D.base (old i0) + 2 * R ≤ depth := by
            exact le_trans (Finset.le_sup (f := fun q : Fin N ↦
              wordNorm D.base (old q) + 2 * R) (Finset.mem_univ i0))
              (le_max_right _ _)
          constructor
          · intro hf
            apply hmDeep
            exact Or.inl (relBall_mono_radius D lam hile
              (by simpa [a, fresh] using hf))
          · intro hf
            apply hmInvDeep
            exact Or.inl (relBall_mono_radius D lam hile
              (by simpa [a, fresh] using hf))
        · intro j0 hij
          have hijVal : i.val < j0.val := hij
          let i0 : Fin N := ⟨i.val, lt_trans hijVal j0.isLt⟩
          have hi0 : i0.castSucc = i := Fin.ext rfl
          rw [← hi0]
          have hij0 : i0 < j0 := hijVal
          simpa [a, Fin.snoc_castSucc] using holdSep i0 j0 hij0

/-! ## The three matched components of a single-base block word -/

/-- A component in `(g h)^n` is the single `h`-letter. -/
theorem componentData_blockWord_singleBase
    (D : RelGenSet G Lambda) (lam : Lambda) {g h v : G} {n i k : ℕ}
    (hg : g ∉ D.fam lam)
    (hc : IsComp lam
      (OsinComponents.blockWord lam [RelLetter.base g] h n) i k) :
    k = i + 1 ∧
      vertex v (OsinComponents.blockWord lam [RelLetter.base g] h n) k =
        vertex v (OsinComponents.blockWord lam [RelLetter.base g] h n) i * h := by
  let w := OsinComponents.blockWord lam [RelLetter.base g] h n
  have hk : k = i + 1 :=
    isComp_succ_of_isWThree (isWThree_blockWord_singleBase D lam hg n) hc
  have hiw : i < w.length := lt_of_lt_of_le hc.1 hc.2.1
  have hlen : w.length = 2 * n := by
    dsimp [w]
    rw [OsinComponents.length_blockWord, List.length_singleton]
    ring
  have hof := hc.2.2.1 i le_rfl hc.1 hiw
  have himod : i % 2 = 1 := by
    have hor : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hor with hzero | hone
    · have heven := getElem_singleBase_even lam g h n i (by omega) hzero hiw
      rw [heven] at hof
      exact False.elim hof
    · exact hone
  have hletter := getElem_singleBase_odd lam g h n i (by omega) himod hiw
  have hv := vertex_succ w v i hiw
  rw [hletter] at hv
  exact ⟨hk, by rw [hk, hv]; rfl⟩

/-- Consecutive components of `(g h)^n` are separated by the literal base
letter `g`. -/
theorem separatorData_blockWord_singleBase
    (D : RelGenSet G Lambda) (lam : Lambda) {g h v : G} {n i k i' k' : ℕ}
    (hg : g ∉ D.fam lam)
    (hc : IsComp lam
      (OsinComponents.blockWord lam [RelLetter.base g] h n) i k)
    (hc' : IsComp lam
      (OsinComponents.blockWord lam [RelLetter.base g] h n) i' k')
    (hstep : BaseEdgeOrTrivial
      (OsinComponents.blockWord lam [RelLetter.base g] h n) k i') :
    i' = k + 1 ∧
      vertex v (OsinComponents.blockWord lam [RelLetter.base g] h n) i' =
        vertex v (OsinComponents.blockWord lam [RelLetter.base g] h n) k * g := by
  let w := OsinComponents.blockWord lam [RelLetter.base g] h n
  obtain ⟨hk, -⟩ := componentData_blockWord_singleBase D lam hg (v := v) hc
  rcases hstep with htrivial | ⟨x, hi', hx⟩
  · subst i'
    exfalso
    have hkw : k < w.length := lt_of_lt_of_le hc'.1 hc'.2.1
    have hnot := hc.2.2.2.2 hkw
    have hyes := hc'.2.2.1 k le_rfl hc'.1 hkw
    exact hnot hyes
  · have hi'w : i' < w.length := lt_of_lt_of_le hc'.1 hc'.2.1
    have hki' : k < i' := by omega
    have hkw : k < w.length := lt_trans hki' hi'w
    have hlen : w.length = 2 * n := by
      dsimp [w]
      rw [OsinComponents.length_blockWord, List.length_singleton]
      ring
    have himod : i % 2 = 1 := by
      have hiw : i < w.length := lt_of_lt_of_le hc.1 hc.2.1
      have hof := hc.2.2.1 i le_rfl hc.1 hiw
      have hor : i % 2 = 0 ∨ i % 2 = 1 := by omega
      rcases hor with hz | ho
      · rw [getElem_singleBase_even lam g h n i (by omega) hz hiw] at hof
        exact False.elim hof
      · exact ho
    have hkmod : k % 2 = 0 := by omega
    have hgget := getElem?_singleBase_even lam g h n k (by omega) hkmod
    have hxg : x = g := by
      rw [hgget] at hx
      exact (RelLetter.base.inj (Option.some.inj hx)).symm
    subst x
    have hv := vertex_succ w v k hkw
    have hget : w[k]'hkw = RelLetter.base g := by
      exact getElem_eq_of_getElem?_eq hkw hgget
    rw [hget] at hv
    exact ⟨hi', by rw [hi', hv]; rfl⟩

/-- In the reversed word, even positions are the inverse peripheral letter. -/
theorem getElem?_rev_blockWord_singleBase_even (lam : Lambda) (g h : G)
    (n j : ℕ) (hj : j < 2 * n) (hmod : j % 2 = 0) :
    (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n))[j]? =
      some (RelLetter.comp lam h⁻¹) := by
  let w := OsinComponents.blockWord lam [RelLetter.base g] h n
  have hlen : w.length = 2 * n := by
    dsimp [w]
    rw [OsinComponents.length_blockWord, List.length_singleton]
    ring
  have hjrev : j < (revWord w).length := by simpa [length_revWord, hlen] using hj
  rw [getElem?_revWord_at w hjrev]
  let r := w.length - 1 - j
  have hr : r < 2 * n := by dsimp [r]; omega
  have hrmod : r % 2 = 1 := by dsimp [r]; omega
  have hrw : r < w.length := by omega
  change some (invLetter (w[r]'hrw)) = some (RelLetter.comp lam h⁻¹)
  rw [getElem_singleBase_odd lam g h n r hr hrmod hrw]
  rfl

/-- In the reversed word, odd positions are the inverse base letter. -/
theorem getElem?_rev_blockWord_singleBase_odd (lam : Lambda) (g h : G)
    (n j : ℕ) (hj : j < 2 * n) (hmod : j % 2 = 1) :
    (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n))[j]? =
      some (RelLetter.base g⁻¹) := by
  let w := OsinComponents.blockWord lam [RelLetter.base g] h n
  have hlen : w.length = 2 * n := by
    dsimp [w]
    rw [OsinComponents.length_blockWord, List.length_singleton]
    ring
  have hjrev : j < (revWord w).length := by simpa [length_revWord, hlen] using hj
  rw [getElem?_revWord_at w hjrev]
  let r := w.length - 1 - j
  have hr : r < 2 * n := by dsimp [r]; omega
  have hrmod : r % 2 = 0 := by dsimp [r]; omega
  have hrw : r < w.length := by omega
  change some (invLetter (w[r]'hrw)) = some (RelLetter.base g⁻¹)
  rw [getElem_singleBase_even lam g h n r hr hrmod hrw]
  rfl

/-- A component in the reversed `(g h)^n` word is the single `h⁻¹`-letter. -/
theorem componentData_rev_blockWord_singleBase
    (D : RelGenSet G Lambda) (lam : Lambda) {g h v : G} {n i k : ℕ}
    (hg : g ∉ D.fam lam)
    (hc : IsComp lam
      (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) i k) :
    k = i + 1 ∧
      vertex v (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) k =
        vertex v (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) i * h⁻¹ := by
  let w := revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)
  have hk : k = i + 1 := isComp_succ_of_isWThree
    (isWThree_revWord D (isWThree_blockWord_singleBase D lam hg n)) hc
  have hiw : i < w.length := lt_of_lt_of_le hc.1 hc.2.1
  have hlen : w.length = 2 * n := by
    dsimp [w]
    rw [length_revWord, OsinComponents.length_blockWord, List.length_singleton]
    ring
  have hof := hc.2.2.1 i le_rfl hc.1 hiw
  have himod : i % 2 = 0 := by
    have hor : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hor with hz | ho
    · exact hz
    · have hodd := getElem?_rev_blockWord_singleBase_odd lam g h n i
          (by omega) ho
      rw [List.getElem?_eq_getElem hiw] at hodd
      have heq := Option.some.inj hodd
      rw [heq] at hof
      exact False.elim hof
  have hget := getElem?_rev_blockWord_singleBase_even lam g h n i
    (by omega) himod
  rw [List.getElem?_eq_getElem hiw] at hget
  have hletter := Option.some.inj hget
  have hv := vertex_succ w v i hiw
  rw [hletter] at hv
  exact ⟨hk, by rw [hk, hv]; rfl⟩

/-- Consecutive reversed components are separated by `g⁻¹`. -/
theorem separatorData_rev_blockWord_singleBase
    (D : RelGenSet G Lambda) (lam : Lambda) {g h v : G} {n i k i' k' : ℕ}
    (hg : g ∉ D.fam lam)
    (hc : IsComp lam
      (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) i k)
    (hc' : IsComp lam
      (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) i' k')
    (hstep : BaseEdgeOrTrivial
      (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n))
      k i') :
    i' = k + 1 ∧
      vertex v (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) i' =
        vertex v (revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)) k * g⁻¹ := by
  let w := revWord (OsinComponents.blockWord lam [RelLetter.base g] h n)
  obtain ⟨hk, -⟩ := componentData_rev_blockWord_singleBase D lam hg (v := v) hc
  rcases hstep with htrivial | ⟨x, hi', hx⟩
  · subst i'
    exfalso
    have hkw : k < w.length := lt_of_lt_of_le hc'.1 hc'.2.1
    have hnot := hc.2.2.2.2 hkw
    have hyes := hc'.2.2.1 k le_rfl hc'.1 hkw
    exact hnot hyes
  · have hi'w : i' < w.length := lt_of_lt_of_le hc'.1 hc'.2.1
    have hki' : k < i' := by omega
    have hkw : k < w.length := lt_trans hki' hi'w
    have hlen : w.length = 2 * n := by
      dsimp [w]
      rw [length_revWord, OsinComponents.length_blockWord,
        List.length_singleton]
      ring
    have himod : i % 2 = 0 := by
      have hiw : i < w.length := lt_of_lt_of_le hc.1 hc.2.1
      have hof := hc.2.2.1 i le_rfl hc.1 hiw
      have hor : i % 2 = 0 ∨ i % 2 = 1 := by omega
      rcases hor with hz | ho
      · exact hz
      · have hodd := getElem?_rev_blockWord_singleBase_odd lam g h n i
            (by omega) ho
        rw [List.getElem?_eq_getElem hiw] at hodd
        rw [Option.some.inj hodd] at hof
        exact False.elim hof
    have hkmod : k % 2 = 1 := by omega
    have hgget := getElem?_rev_blockWord_singleBase_odd lam g h n k
      (by omega) hkmod
    have hxg : x = g⁻¹ := by
      rw [hgget] at hx
      exact (RelLetter.base.inj (Option.some.inj hx)).symm
    subst x
    have hv := vertex_succ w v k hkw
    have hget : w[k]'hkw = RelLetter.base g⁻¹ :=
      getElem_eq_of_getElem?_eq hkw hgget
    rw [hget] at hv
    exact ⟨hi', by rw [hi', hv]; rfl⟩

/-! ## The middle-component estimate -/

/-- Three matched components, with literal one-base-letter separators on both
paths, force the first path's middle peripheral label to be shallow relative
to the second path's middle label. -/
theorem middleMatchedLetter_mem_relBall
    (D : RelGenSet G Lambda) (hbase : IsSymmetricGeneratingSet D.base)
    (R : ℕ)
    (hrect : ∀ (lam : Lambda) (x y r s : G),
      x ∈ D.fam lam → y ∈ D.fam lam →
      r ∈ D.base → s ∈ D.base → r ∉ D.fam lam →
      s ∉ D.fam lam → x * s = r * y →
      x ∈ D.relBall lam R ∧ y ∈ D.relBall lam R)
    {lam : Lambda} {p q : List (RelLetter G Lambda)} {vp vq : G}
    {ip kp iq kq : ℕ → ℕ} {u v r s : G}
    (hpLetter : vertex vp p (kp 1) = vertex vp p (ip 1) * u)
    (hqLetter : vertex vq q (kq 1) = vertex vq q (iq 1) * v)
    (hpSep0 : vertex vp p (ip 1) = vertex vp p (kp 0) * r)
    (hqSep0 : vertex vq q (iq 1) = vertex vq q (kq 0) * s)
    (hpSep1 : vertex vp p (ip 2) = vertex vp p (kp 1) * r)
    (hqSep1 : vertex vq q (iq 2) = vertex vq q (kq 1) * s)
    (hcompP : ∀ t : ℕ, t < 3 → IsComp lam p (ip t) (kp t))
    (hcompQ : ∀ t : ℕ, t < 3 → IsComp lam q (iq t) (kq t))
    (hletterP : ∀ c ∈ p, D.IsLetter c)
    (hletterQ : ∀ c ∈ q, D.IsLetter c)
    (hstart : ∀ t : ℕ, t < 3 →
      (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam lam)
    (hu : u ∈ D.fam lam) (hv : v ∈ D.fam lam)
    (hr : r ∈ D.base) (hs : s ∈ D.base)
    (hrnot : r ∉ D.fam lam) (hsnot : s ∉ D.fam lam) :
    u ∈ D.relBall lam (wordNorm D.base v + 2 * R) := by
  let c : ℕ → G := fun t ↦
    (vertex vp p (ip t))⁻¹ * vertex vq q (iq t)
  let e : ℕ → G := fun t ↦
    (vertex vp p (kp t))⁻¹ * vertex vq q (kq t)
  have hc : ∀ t : ℕ, t < 3 → c t ∈ D.fam lam := hstart
  have he : ∀ t : ℕ, t < 3 → e t ∈ D.fam lam := by
    intro t ht
    exact WWord.endConnector_mem_fam D hletterP hletterQ
      (hcompP t ht) (hcompQ t ht) (hstart t ht)
  have hclose0 : e 0 * s = r * c 1 := by
    dsimp [e, c]
    rw [hpSep0, hqSep0]
    group
  have hclose1 : e 1 * s = r * c 2 := by
    dsimp [e, c]
    rw [hpSep1, hqSep1]
    group
  obtain ⟨-, hc1R⟩ := hrect lam (e 0) (c 1) r s
    (he 0 (by omega)) (hc 1 (by omega)) hr hs hrnot hsnot hclose0
  obtain ⟨he1R, -⟩ := hrect lam (e 1) (c 2) r s
    (he 1 (by omega)) (hc 2 (by omega)) hr hs hrnot hsnot hclose1
  have hvR : v ∈ D.relBall lam (wordNorm D.base v) :=
    mem_relBall_of_wordNorm_le hbase hv le_rfl
  have heInvR := relBall_inv D lam hbase.inv_mem he1R
  have hprod := relBall_mul D lam hc1R (relBall_mul D lam hvR heInvR)
  have huEq : u = c 1 * v * (e 1)⁻¹ := by
    dsimp [c, e]
    rw [hpLetter, hqLetter]
    group
  rw [huEq]
  convert hprod using 1
  · exact mul_assoc (c 1) v ((e 1)⁻¹)
  · ring

/-! ## DGO Corollary 6.12, finite-family form -/

/-- **The power clause of DGO Corollary 6.12 with pairwise
non-commensurability.**  The only literature input is `DGOLemma421b`; the
loxodromy threshold and all fixed-side polygon bounds are already theorems.
-/
theorem exists_pairwiseNonCommensurable_mul_powers_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {h g : G} (hlox : IsLoxodromic h (Cayley.base A.alphabet))
    (hgE : g ∉ elementaryClosure h) (extra : Set G) (hextra : extra.Finite)
    (N : ℕ) :
    ∃ a : Fin N → G,
      (∀ j, ∃ m : ℕ, 0 < m ∧ a j = h ^ m) ∧
      (∀ j, a j ∉ extra ∧ (a j)⁻¹ ∉ extra) ∧
      (∀ j, IsLoxodromic (g * a j) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable (fun j ↦ g * a j) := by
  let E : Unit → Subgroup G := fun _ ↦ elementaryClosure h
  let D0 : RelGenSet G Unit := coneOffFamily A.alphabet E
  have hemb0 : D0.IsHyperbolicallyEmbedded := by
    exact isHyperbolicallyEmbedded_elementaryClosure_family A
      (fun _ : Unit ↦ h)
      (pairwiseNonCommensurable_of_subsingleton (fun _ : Unit ↦ h))
      (fun _ ↦ hlox)
  let D : RelGenSet G Unit := D0.adjoinPair g
  have hemb : D.IsHyperbolicallyEmbedded := by
    exact (RelGenSet.dgoCorollary427 G Unit D0 D rfl
      (RelGenSet.finite_base_symmDiff_adjoinPair D0 g)).mp hemb0
  have hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet) :=
    hemb.hyperbolic
  have hbaseD : IsSymmetricGeneratingSet D.base := by
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [D, D0, RelGenSet.adjoinPair_base, coneOffFamily_base,
        Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with hx | rfl | rfl
      · exact Or.inl (A.alphabet.symmetricGenerating.inv_mem x hx)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl (inv_inv g))
    · apply eq_top_iff.mpr
      rw [← A.alphabet.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono (by
        intro x hx
        simpa [D, D0] using (RelGenSet.base_subset_adjoinPair D0 g hx))
  have hgBase : g ∈ D.base := by
    exact Or.inr (Or.inl rfl)
  have hgInvBase : g⁻¹ ∈ D.base := hbaseD.inv_mem g hgBase
  have hgFam : g ∉ D.fam () := by simpa [D, D0, E] using hgE
  have hgLetter : ∀ c ∈ ([RelLetter.base g] : List (RelLetter G Unit)),
      D.IsLetter c := by
    intro c hc
    have hc' : c = RelLetter.base g := List.mem_singleton.mp hc
    subst c
    exact hgBase
  let wg : List (RelLetter G Unit) := [RelLetter.base g]
  have hwgLetter : ∀ c ∈ wg, D.IsLetter c := by
    intro c hc
    have hc' : c = RelLetter.base g := by simpa [wg] using hc
    subst c
    exact hgBase
  have hwgValue : RelLetter.listVal wg = g := by
    simp [wg, RelLetter.listVal, RelLetter.val]
  have hwgNo : ∀ c ∈ wg, ¬ c.IsCompOf () := by
    intro c hc
    have hc' : c = RelLetter.base g := by simpa [wg] using hc
    subst c
    exact id
  obtain ⟨Clox, hClox⟩ := exists_threshold_isLoxodromic_mul_of_symm
    D () hbaseD.inv_mem hhyp hgFam
      wg hwgLetter hwgValue hwgNo
  obtain ⟨Cmatch, hraw⟩ := h421b G Unit D hhyp
  obtain ⟨deltaD, hdeltaD⟩ := hhyp
  have hfour : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier ⌈deltaD⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdeltaD
  obtain ⟨Rrect, hrect⟩ := exists_radius_connectors_of_base_rectangle
    D hbaseD hfour
  have hinj : Function.Injective (fun n : ℕ ↦ h ^ n) :=
    injective_pow_of_not_isOfFinOrder (not_isOfFinOrder_of_isLoxodromic hlox)
  obtain ⟨a, haPow, haDeep, haExtra, haSep⟩ := exists_successivelySeparatedPowers
    D () hbaseD (hemb.locallyFinite ()) hinj
      extra hextra (max Clox Cmatch) Rrect N
  have haMem : ∀ j, a j ∈ D.fam () := by
    intro j
    obtain ⟨m, -, hm⟩ := haPow j
    rw [hm]
    simpa [D, D0, E] using
      (zpowers_le_elementaryClosure h
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) m))
  have haDeepLox : ∀ j, a j ∉ D.relBall () Clox := by
    intro j
    exact notMem_relBall_of_le (le_max_left _ _) (haDeep j).1
  have haDeepMatch : ∀ j, a j ∉ D.relBall () Cmatch := by
    intro j
    exact notMem_relBall_of_le (le_max_right _ _) (haDeep j).1
  have hloxEnlarged : ∀ j,
      IsLoxodromic (g * a j) (Cayley.base D.alphabet) :=
    fun j ↦ hClox (a j) (haMem j) (haDeepLox j)
  have hbaseSubset : A.alphabet.carrier ⊆ D.alphabet.carrier := by
    intro x hx
    apply base_subset_alphabet_carrier D
    exact Or.inl hx
  refine ⟨a, haPow, haExtra,
    isLoxodromic_base_of_subset_family hbaseSubset hloxEnlarged, ?_⟩
  have hnotCommLt : ∀ i j : Fin N, i < j →
      ∀ (p q : ℤ), p ≠ 0 → q ≠ 0 → ∀ t : G,
        t * (g * a i) ^ p * t⁻¹ ≠ (g * a j) ^ q := by
    intro i j hij p q hp hq t hbad
    obtain ⟨n, m, hn, hm, hsame | hopp⟩ :=
      exists_positive_conjugatePower_eq_or_inv hp hq hbad
    · let K : ℕ := 3
      let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
      have heps : 0 < eps := by dsimp [eps]; positivity
      obtain ⟨R, -, hmatch⟩ := hraw eps K heps (by simp [K])
      let Ni := n * R
      let Nj := m * R
      let wi := OsinComponents.blockWord () [RelLetter.base g] (a i) Ni
      let wj := OsinComponents.blockWord () [RelLetter.base g] (a j) Nj
      have hlength : R ≤ wj.length := by
        dsimp [wj, Nj]
        rw [OsinComponents.length_blockWord, List.length_singleton]
        have hR : R ≤ m * R := Nat.le_mul_of_pos_left R hm
        omega
      have hsameR : t * (g * a i) ^ Ni * t⁻¹ = (g * a j) ^ Nj := by
        dsimp [Ni, Nj]
        calc
          t * (g * a i) ^ (n * R) * t⁻¹ =
              (t * (g * a i) ^ n * t⁻¹) ^ R := by rw [pow_mul, conj_pow]
          _ = ((g * a j) ^ m) ^ R := by rw [hsame]
          _ = (g * a j) ^ (m * R) := by rw [pow_mul]
      have hcommuteR : t * (g * a i) ^ Ni = (g * a j) ^ Nj * t := by
        calc
          t * (g * a i) ^ Ni = (t * (g * a i) ^ Ni * t⁻¹) * t := by group
          _ = (g * a j) ^ Nj * t := by rw [hsameR]
      have hletterI : ∀ c ∈ wi, D.IsLetter c := by
        dsimp [wi]
        exact isLetter_of_mem_blockWord D () hgLetter (haMem i) Ni
      have hletterJ : ∀ c ∈ wj, D.IsLetter c := by
        dsimp [wj]
        exact isLetter_of_mem_blockWord D () hgLetter (haMem j) Nj
      have hvalI : RelLetter.listVal wi = (g * a i) ^ Ni := by
        dsimp [wi]
        rw [OsinComponents.listVal_blockWord,
          OsinComponents.listVal_singleton]
        rfl
      have hvalJ : RelLetter.listVal wj = (g * a j) ^ Nj := by
        dsimp [wj]
        rw [OsinComponents.listVal_blockWord,
          OsinComponents.listVal_singleton]
        rfl
      have hstartDist : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
        dsimp [eps]
        norm_num
      have hendDist :
          (wordDist D.alphabet.carrier (vertex 1 wj wj.length)
            (vertex t wi wi.length) : ℝ) ≤ eps := by
        simp only [vertex_length, hvalJ, hvalI, one_mul]
        rw [hcommuteR]
        have hd := wordDist_left_invariant D.alphabet.carrier
          ((g * a j) ^ Nj)⁻¹ ((g * a j) ^ Nj) ((g * a j) ^ Nj * t)
        have hsimp : ((g * a j) ^ Nj)⁻¹ * ((g * a j) ^ Nj * t) = t := by group
        rw [inv_mul_cancel, hsimp] at hd
        calc
          (wordDist D.alphabet.carrier ((g * a j) ^ Nj)
              ((g * a j) ^ Nj * t) : ℝ) =
              (wordDist D.alphabet.carrier 1 t : ℝ) := by exact_mod_cast hd.symm
          _ ≤ eps := hstartDist
      obtain ⟨ip, kp, iq, kq, lam, hcompJ, hcompI,
          hstepJ, hstepI, hstarts⟩ :=
        hmatch 1 t wj wi hletterJ hletterI
          (isWOne_blockWord_singleBase () g (a j) Nj)
          (isWTwo_blockWord_singleBase D () (haDeepMatch j) Nj)
          (isWThree_blockWord_singleBase D () hgFam Nj)
          (isWOne_blockWord_singleBase () g (a i) Ni)
          (isWTwo_blockWord_singleBase D () (haDeepMatch i) Ni)
          (isWThree_blockWord_singleBase D () hgFam Ni)
          hlength hstartDist hendDist
      have hcompJ' : ∀ z : ℕ, z < 3 → IsComp () wj (ip z) (kp z) :=
        fun z hz ↦ by simpa using hcompJ z hz
      have hcompI' : ∀ z : ℕ, z < 3 → IsComp () wi (iq z) (kq z) :=
        fun z hz ↦ by simpa using hcompI z hz
      obtain ⟨-, hpLetter⟩ := componentData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 1 (by omega))
      obtain ⟨-, hqLetter⟩ := componentData_blockWord_singleBase
        D () hgFam (v := t) (hcompI' 1 (by omega))
      obtain ⟨-, hpSep0⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 0 (by omega))
          (hcompJ' 1 (by omega)) (hstepJ 0 (by simp [K]))
      obtain ⟨-, hqSep0⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := t) (hcompI' 0 (by omega))
          (hcompI' 1 (by omega)) (hstepI 0 (by simp [K]))
      obtain ⟨-, hpSep1⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 1 (by omega))
          (hcompJ' 2 (by omega)) (hstepJ 1 (by simp [K]))
      obtain ⟨-, hqSep1⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := t) (hcompI' 1 (by omega))
          (hcompI' 2 (by omega)) (hstepI 1 (by simp [K]))
      have hshallow := middleMatchedLetter_mem_relBall D
        hbaseD Rrect hrect hpLetter hqLetter
        hpSep0 hqSep0 hpSep1 hqSep1 hcompJ' hcompI' hletterJ hletterI
        (fun z hz ↦ by simpa using hstarts z hz)
        (haMem j) (haMem i) hgBase hgBase
        hgFam hgFam
      exact (haSep i j hij).1 hshallow
    · let K : ℕ := 3
      let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
      have heps : 0 < eps := by dsimp [eps]; positivity
      obtain ⟨R, -, hmatch⟩ := hraw eps K heps (by simp [K])
      let Ni := n * R
      let Nj := m * R
      let wi := OsinComponents.blockWord () [RelLetter.base g] (a i) Ni
      let wj := OsinComponents.blockWord () [RelLetter.base g] (a j) Nj
      have hlength : R ≤ wj.length := by
        dsimp [wj, Nj]
        rw [OsinComponents.length_blockWord, List.length_singleton]
        have hR : R ≤ m * R := Nat.le_mul_of_pos_left R hm
        omega
      have hoppR : t * (g * a i) ^ Ni * t⁻¹ = ((g * a j) ^ Nj)⁻¹ := by
        dsimp [Ni, Nj]
        calc
          t * (g * a i) ^ (n * R) * t⁻¹ =
              (t * (g * a i) ^ n * t⁻¹) ^ R := by rw [pow_mul, conj_pow]
          _ = (((g * a j) ^ m)⁻¹) ^ R := by rw [hopp]
          _ = ((g * a j) ^ (m * R))⁻¹ := by rw [pow_mul, inv_pow]
      have hinverseR : t * ((g * a i) ^ Ni)⁻¹ = (g * a j) ^ Nj * t := by
        have hc : t * ((g * a i) ^ Ni)⁻¹ * t⁻¹ = (g * a j) ^ Nj := by
          calc
            t * ((g * a i) ^ Ni)⁻¹ * t⁻¹ =
                (t * (g * a i) ^ Ni * t⁻¹)⁻¹ := by group
            _ = (((g * a j) ^ Nj)⁻¹)⁻¹ := by rw [hoppR]
            _ = (g * a j) ^ Nj := inv_inv _
        calc
          t * ((g * a i) ^ Ni)⁻¹ =
              (t * ((g * a i) ^ Ni)⁻¹ * t⁻¹) * t := by group
          _ = (g * a j) ^ Nj * t := by rw [hc]
      have hletterJ : ∀ c ∈ wj, D.IsLetter c := by
        dsimp [wj]
        exact isLetter_of_mem_blockWord D () hgLetter (haMem j) Nj
      have hletterRevI : ∀ c ∈ revWord wi, D.IsLetter c :=
        isLetter_of_mem_revWord D hbaseD.inv_mem (by
          dsimp [wi]
          exact isLetter_of_mem_blockWord D () hgLetter (haMem i) Ni)
      have hvalI : RelLetter.listVal wi = (g * a i) ^ Ni := by
        dsimp [wi]
        rw [OsinComponents.listVal_blockWord,
          OsinComponents.listVal_singleton]
        rfl
      have hvalJ : RelLetter.listVal wj = (g * a j) ^ Nj := by
        dsimp [wj]
        rw [OsinComponents.listVal_blockWord,
          OsinComponents.listVal_singleton]
        rfl
      have hvalRevI : RelLetter.listVal (revWord wi) =
          ((g * a i) ^ Ni)⁻¹ := by
        rw [listVal_revWord, hvalI]
      have hstartDist : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
        dsimp [eps]
        norm_num
      have hendDist :
          (wordDist D.alphabet.carrier (vertex 1 wj wj.length)
            (vertex t (revWord wi) (revWord wi).length) : ℝ) ≤ eps := by
        simp only [vertex_length, hvalJ, hvalRevI, one_mul]
        rw [hinverseR]
        have hd := wordDist_left_invariant D.alphabet.carrier
          ((g * a j) ^ Nj)⁻¹ ((g * a j) ^ Nj) ((g * a j) ^ Nj * t)
        have hsimp : ((g * a j) ^ Nj)⁻¹ * ((g * a j) ^ Nj * t) = t := by group
        rw [inv_mul_cancel, hsimp] at hd
        calc
          (wordDist D.alphabet.carrier ((g * a j) ^ Nj)
              ((g * a j) ^ Nj * t) : ℝ) =
              (wordDist D.alphabet.carrier 1 t : ℝ) := by exact_mod_cast hd.symm
          _ ≤ eps := hstartDist
      obtain ⟨ip, kp, iq, kq, lam, hcompJ, hcompRevI,
          hstepJ, hstepRevI, hstarts⟩ :=
        hmatch 1 t wj (revWord wi) hletterJ hletterRevI
          (isWOne_blockWord_singleBase () g (a j) Nj)
          (isWTwo_blockWord_singleBase D () (haDeepMatch j) Nj)
          (isWThree_blockWord_singleBase D () hgFam Nj)
          (isWOne_revWord (isWOne_blockWord_singleBase () g (a i) Ni))
          (isWTwo_revWord D hbaseD.inv_mem
            (isWTwo_blockWord_singleBase D () (haDeepMatch i) Ni))
          (isWThree_revWord D (isWThree_blockWord_singleBase D () hgFam Ni))
          hlength hstartDist hendDist
      have hcompJ' : ∀ z : ℕ, z < 3 → IsComp () wj (ip z) (kp z) :=
        fun z hz ↦ by simpa using hcompJ z hz
      have hcompRevI' : ∀ z : ℕ, z < 3 →
          IsComp () (revWord wi) (iq z) (kq z) :=
        fun z hz ↦ by simpa using hcompRevI z hz
      obtain ⟨-, hpLetter⟩ := componentData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 1 (by omega))
      obtain ⟨-, hqLetter⟩ := componentData_rev_blockWord_singleBase
        D () hgFam (v := t) (hcompRevI' 1 (by omega))
      obtain ⟨-, hpSep0⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 0 (by omega))
          (hcompJ' 1 (by omega)) (hstepJ 0 (by simp [K]))
      obtain ⟨-, hqSep0⟩ := separatorData_rev_blockWord_singleBase
        D () hgFam (v := t) (hcompRevI' 0 (by omega))
          (hcompRevI' 1 (by omega)) (hstepRevI 0 (by simp [K]))
      obtain ⟨-, hpSep1⟩ := separatorData_blockWord_singleBase
        D () hgFam (v := (1 : G)) (hcompJ' 1 (by omega))
          (hcompJ' 2 (by omega)) (hstepJ 1 (by simp [K]))
      obtain ⟨-, hqSep1⟩ := separatorData_rev_blockWord_singleBase
        D () hgFam (v := t) (hcompRevI' 1 (by omega))
          (hcompRevI' 2 (by omega)) (hstepRevI 1 (by simp [K]))
      have hgInvE : g⁻¹ ∉ D.fam () := by
        intro hgInv
        exact hgFam (by simpa using inv_mem hgInv)
      have hshallow := middleMatchedLetter_mem_relBall D
        hbaseD Rrect hrect hpLetter hqLetter
        hpSep0 hqSep0 hpSep1 hqSep1 hcompJ' hcompRevI' hletterJ hletterRevI
        (fun z hz ↦ by simpa using hstarts z hz)
        (haMem j) (inv_mem (haMem i))
        hgBase hgInvBase hgFam hgInvE
      have hnorm : wordNorm D.base (a i)⁻¹ = wordNorm D.base (a i) :=
        wordNorm_inv hbaseD (a i)
      rw [hnorm] at hshallow
      exact (haSep i j hij).1 hshallow
  intro i j hij p q hp hq t
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hnotCommLt i j hijlt p q hp hq t
  · intro hbad
    apply hnotCommLt j i hjilt q p hq hp t⁻¹
    calc
      t⁻¹ * (g * a j) ^ q * (t⁻¹)⁻¹ =
          t⁻¹ * (t * (g * a i) ^ p * t⁻¹) * t := by
            rw [hbad, inv_inv]
      _ = (g * a i) ^ p := by group

end HullSC
end GroupApproximation
