import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSeparable

/-!
# Purely large ideals: definitions and elementary estimates

Lane TWWSch3c3, work order WO-TWWSch-3c-3 (C. Schafhauser, *Subalgebras of simple
AF-algebras*, Ann. of Math. 192 (2020), §3--4; *A new proof of the Tikuisis--White--Winter
theorem*, J. reine angew. Math. 759 (2020), §4).

An extension `0 → I → D → D/I → 0` is *purely large* (Elliott--Kucerovsky, *An abstract
Voiculescu--Brown--Douglas--Fillmore absorption theorem*, Pacific J. Math. 198 (2001))
when for every `e ∈ D \ I` the hereditary cut `closure (e I e*)` contains a stable
`C*`-subalgebra that is full in `I`.  Stability is recorded through the
Hjelmborg--Rørdam criterion (J. Hjelmborg, M. Rørdam, *On stability of C*-algebras*,
J. Funct. Anal. 155 (1998), Thm 2.1 and Prop 2.2): a σ-unital `C` is stable iff for all
`c ∈ C` and `ε > 0` there is `x ∈ C` with `‖x*x − c*c‖ < ε` and `‖x x* c*c‖ < ε`.

This file contains:

* `conjSet`, `hereditaryCut`, `IsHRStable`, `IsFullIn`, `IsPurelyLargeIdeal`;
* `cutSubalgebra`: the cut of an ideal `D ∩ J` is a non-unital star subalgebra;
* `isPurelyLargeIdeal_of_cut`: it suffices to check the cut itself;
* norm estimates for perturbing the Hjelmborg--Rørdam quantities, and
  `isHRStable_closure`: the criterion passes from a set to its closure.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

open TopologicalSpace

variable {B : Type} [CStarAlgebra B]

/-- The conjugates `d j d*` of the elements `j ∈ I`. -/
def conjSet (d : B) (I : Set B) : Set B :=
  {y | ∃ j ∈ I, y = d * j * star d}

theorem mem_conjSet {d y : B} {I : Set B} : y ∈ conjSet d I ↔ ∃ j ∈ I, y = d * j * star d :=
  Iff.rfl

/-- The hereditary cut `closure (d I d*)`. -/
def hereditaryCut (d : B) (I : Set B) : Set B :=
  closure (conjSet d I)

/-- The Hjelmborg--Rørdam stability condition (JFA 155 (1998), Prop 2.2). -/
def IsHRStable (C : Set B) : Prop :=
  ∀ c ∈ C, ∀ ε : ℝ, 0 < ε → ∃ x ∈ C,
    ‖star x * x - star c * c‖ < ε ∧ ‖x * star x * (star c * c)‖ < ε

/-- `C` is full in `I`: every element of `I` is a limit of finite sums of products
`a c b` with `a, b ∈ I` and `c ∈ C`. -/
def IsFullIn (C I : Set B) : Prop :=
  I ⊆ closure ((Submodule.span ℂ {y | ∃ a ∈ I, ∃ c ∈ C, ∃ b ∈ I, y = a * c * b} :
    Submodule ℂ B) : Set B)

/-- The extension `0 → D ∩ J → D → D/(D ∩ J) → 0` is purely large: for each `e ∈ D \ J`
the cut `closure (e (D ∩ J) e*)` contains a closed separable star subalgebra that
satisfies the Hjelmborg--Rørdam condition and is full in `D ∩ J`. -/
def IsPurelyLargeIdeal (D : StarSubalgebra ℂ B) (J : NonUnitalStarSubalgebra ℂ B) : Prop :=
  ∀ e ∈ D, e ∉ J → ∃ C : NonUnitalStarSubalgebra ℂ B,
    (C : Set B) ⊆ hereditaryCut e (sepIdeal D J) ∧ IsClosed (C : Set B) ∧
      IsSeparable (C : Set B) ∧ IsHRStable (C : Set B) ∧ IsFullIn (C : Set B) (sepIdeal D J)

/-- For `e ∈ D` and a right ideal `J`, the conjugates `e (D ∩ J) e*` form a non-unital
star subalgebra, since `(e j e*)(e j' e*) = e (j e*e j') e*`. -/
def cutSubalgebra (D : StarSubalgebra ℂ B) (J : NonUnitalStarSubalgebra ℂ B)
    (hJR : ∀ b x : B, x ∈ J → x * b ∈ J) {e : B} (he : e ∈ D) :
    NonUnitalStarSubalgebra ℂ B where
  carrier := conjSet e (sepIdeal D J)
  add_mem' := by
    intro y y' hy hy'
    obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
    obtain ⟨j', hj', rfl⟩ := mem_conjSet.mp hy'
    have hj0 : j ∈ sepIdeal D J := SetLike.mem_coe.mp hj
    have hj0' : j' ∈ sepIdeal D J := SetLike.mem_coe.mp hj'
    exact mem_conjSet.mpr ⟨j + j', SetLike.mem_coe.mpr (add_mem hj0 hj0'),
      by rw [mul_add, add_mul]⟩
  zero_mem' := mem_conjSet.mpr ⟨0, SetLike.mem_coe.mpr (zero_mem (sepIdeal D J)),
    by rw [mul_zero, zero_mul]⟩
  mul_mem' := by
    intro y y' hy hy'
    obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
    obtain ⟨j', hj', rfl⟩ := mem_conjSet.mp hy'
    have hj0 : j ∈ sepIdeal D J := SetLike.mem_coe.mp hj
    have hj0' : j' ∈ sepIdeal D J := SetLike.mem_coe.mp hj'
    have hee : star e * e ∈ D := mul_mem (star_mem he) he
    refine mem_conjSet.mpr ⟨j * (star e * e) * j',
      SetLike.mem_coe.mpr (mul_mem (mul_mem_sepIdeal_right hJR hee hj0) hj0'), ?_⟩
    simp only [mul_assoc]
  smul_mem' := by
    intro r y hy
    obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
    have hj0 : j ∈ sepIdeal D J := SetLike.mem_coe.mp hj
    exact mem_conjSet.mpr ⟨r • j, SetLike.mem_coe.mpr (SMulMemClass.smul_mem r hj0),
      by rw [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
    have hj0 : j ∈ sepIdeal D J := SetLike.mem_coe.mp hj
    exact mem_conjSet.mpr ⟨star j, SetLike.mem_coe.mpr (star_mem hj0),
      by rw [star_mul, star_mul, star_star, mul_assoc]⟩

/-- **Checking pure largeness on the cut itself.**  If `D` is closed and separable and
every cut `closure (e (D ∩ J) e*)` with `e ∈ D \ J` satisfies the Hjelmborg--Rørdam
condition and is full in `D ∩ J`, the extension is purely large. -/
theorem isPurelyLargeIdeal_of_cut {D : StarSubalgebra ℂ B} {J : NonUnitalStarSubalgebra ℂ B}
    (hD : IsSepClosed D) (hJR : ∀ b x : B, x ∈ J → x * b ∈ J)
    (h : ∀ e ∈ D, e ∉ J → IsHRStable (hereditaryCut e (sepIdeal D J)) ∧
      IsFullIn (hereditaryCut e (sepIdeal D J)) (sepIdeal D J)) :
    IsPurelyLargeIdeal D J := by
  intro e he heJ
  have hsub : conjSet e (sepIdeal D J) ⊆ (D : Set B) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := mem_conjSet.mp hy
    have hj0 : j ∈ sepIdeal D J := SetLike.mem_coe.mp hj
    exact SetLike.mem_coe.mpr (mul_mem (mul_mem he (mem_sepIdeal.mp hj0).1) (star_mem he))
  refine ⟨(cutSubalgebra D J hJR he).topologicalClosure, fun _ hx => hx,
    NonUnitalStarSubalgebra.isClosed_topologicalClosure _,
    hD.2.mono (closure_minimal hsub hD.1), (h e he heJ).1, (h e he heJ).2⟩

/-- `‖a b − a' b'‖ ≤ ‖a − a'‖ ‖b‖ + ‖a'‖ ‖b − b'‖`. -/
theorem norm_mul_sub_mul_le (a b a' b' : B) :
    ‖a * b - a' * b'‖ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by
    rw [sub_mul, mul_sub]
    abel
  calc ‖a * b - a' * b'‖ = ‖(a - a') * b + a' * (b - b')‖ := by rw [h]
    _ ≤ ‖(a - a') * b‖ + ‖a' * (b - b')‖ := norm_add_le _ _
    _ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)

/-- `‖w*w − w'*w'‖ ≤ 2 L η` when `‖w‖, ‖w'‖ ≤ L` and `‖w − w'‖ ≤ η`. -/
theorem norm_star_mul_sub_star_mul_le (w w' : B) {L η : ℝ} (hw : ‖w‖ ≤ L) (hw' : ‖w'‖ ≤ L)
    (hη : ‖w - w'‖ ≤ η) : ‖star w * w - star w' * w'‖ ≤ 2 * L * η := by
  have h1 := norm_mul_sub_mul_le (star w) w (star w') w'
  rw [← star_sub, norm_star, norm_star] at h1
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have h2 : ‖w - w'‖ * ‖w‖ ≤ η * L := mul_le_mul hη hw (norm_nonneg _) hη0
  have h3 : ‖w'‖ * ‖w - w'‖ ≤ L * η := mul_le_mul hw' hη (norm_nonneg _) ((norm_nonneg _).trans hw')
  linarith

/-- **Perturbing the Hjelmborg--Rørdam quantities.** -/
theorem hr_perturb (u v u' v' : B) {L η : ℝ} (hu : ‖u‖ ≤ L) (hu' : ‖u'‖ ≤ L) (hv : ‖v‖ ≤ L)
    (hv' : ‖v'‖ ≤ L) (huη : ‖u - u'‖ ≤ η) (hvη : ‖v - v'‖ ≤ η) :
    ‖star u * u - star v * v‖ ≤ ‖star u' * u' - star v' * v'‖ + 4 * L * η ∧
      ‖u * star u * (star v * v)‖ ≤
        ‖u' * star u' * (star v' * v')‖ + 4 * (L * L * L) * η := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hu
  have hη : 0 ≤ η := (norm_nonneg _).trans huη
  have hsu := norm_star_mul_sub_star_mul_le u u' hu hu' huη
  have hsv := norm_star_mul_sub_star_mul_le v v' hv hv' hvη
  constructor
  · have h1 : star u * u - star v * v = (star u' * u' - star v' * v') +
        ((star u * u - star u' * u') - (star v * v - star v' * v')) := by abel
    have h2 := norm_add_le (star u' * u' - star v' * v')
      ((star u * u - star u' * u') - (star v * v - star v' * v'))
    have h3 := norm_sub_le (star u * u - star u' * u') (star v * v - star v' * v')
    rw [← h1] at h2
    linarith
  · have hw : ‖u * star u - u' * star u'‖ ≤ 2 * L * η := by
      have h1 := norm_mul_sub_mul_le u (star u) u' (star u')
      rw [← star_sub, norm_star, norm_star] at h1
      have h2 : ‖u - u'‖ * ‖u‖ ≤ η * L := mul_le_mul huη hu (norm_nonneg _) hη
      have h3 : ‖u'‖ * ‖u - u'‖ ≤ L * η := mul_le_mul hu' huη (norm_nonneg _) hL
      linarith
    have hW : ‖star v * v‖ ≤ L * L := (norm_mul_le (star v) v).trans
      (by rw [norm_star]; exact mul_le_mul hv hv (norm_nonneg _) hL)
    have hV : ‖u' * star u'‖ ≤ L * L := (norm_mul_le u' (star u')).trans
      (by rw [norm_star]; exact mul_le_mul hu' hu' (norm_nonneg _) hL)
    have h2L : 0 ≤ 2 * L * η := mul_nonneg (mul_nonneg (by norm_num) hL) hη
    have h1 := norm_mul_sub_mul_le (u * star u) (star v * v) (u' * star u') (star v' * v')
    have h2 : ‖u * star u - u' * star u'‖ * ‖star v * v‖ ≤ (2 * L * η) * (L * L) :=
      mul_le_mul hw hW (norm_nonneg _) h2L
    have h3 : ‖u' * star u'‖ * ‖star v * v - star v' * v'‖ ≤ (L * L) * (2 * L * η) :=
      mul_le_mul hV hsv (norm_nonneg _) (mul_nonneg hL hL)
    have h4 := norm_le_norm_add_norm_sub' (u * star u * (star v * v))
      (u' * star u' * (star v' * v'))
    linarith

/-- **The Hjelmborg--Rørdam condition passes to closures.**  It is enough to find
witnesses in `closure S` for the elements of `S`. -/
theorem isHRStable_closure {S : Set B}
    (h : ∀ c ∈ S, ∀ ε : ℝ, 0 < ε → ∃ x ∈ closure S,
      ‖star x * x - star c * c‖ < ε ∧ ‖x * star x * (star c * c)‖ < ε) :
    IsHRStable (closure S) := by
  intro c hc ε hε
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ‖c‖ + 1 + ε := ⟨_, rfl⟩
  have hc0 := norm_nonneg c
  have hL : 0 ≤ L := by rw [hLdef]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = L * L * L + L + 1 := ⟨_, rfl⟩
  have hLLL : 0 ≤ L * L * L := mul_nonneg (mul_nonneg hL hL) hL
  have hM : 0 < 8 * M := by rw [hMdef]; linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (8 * M) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact div_pos hε hM
  have h8 : 8 * M * η = ε := by rw [hηdef]; exact mul_div_cancel₀ ε hM.ne'
  obtain ⟨c', hc'S, hcc'⟩ := Metric.mem_closure_iff.mp hc (min 1 η) (lt_min one_pos hη)
  rw [dist_eq_norm] at hcc'
  have hcc1 : ‖c - c'‖ ≤ 1 := hcc'.le.trans (min_le_left _ _)
  have hccη : ‖c - c'‖ ≤ η := hcc'.le.trans (min_le_right _ _)
  have hc' : ‖c'‖ ≤ ‖c‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c' c
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨x, hxS, hx1, hx2⟩ := h c' hc'S (ε / 2) (half_pos hε)
  have hxL : ‖x‖ ≤ L := by
    have hxx : ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self
    have hcc : ‖star c' * c'‖ = ‖c'‖ * ‖c'‖ := CStarRing.norm_star_mul_self
    have h1 := norm_le_norm_add_norm_sub' (star x * x) (star c' * c')
    have h2 : ‖c'‖ * ‖c'‖ ≤ (‖c‖ + 1) * (‖c‖ + 1) :=
      mul_le_mul hc' hc' (norm_nonneg _) (by positivity)
    have h3 : (‖c‖ + 1) * (‖c‖ + 1) + ε / 2 ≤ L * L := by
      rw [hLdef]
      nlinarith [hε.le, hc0]
    exact nonneg_le_nonneg_of_sq_le_sq hL (by linarith)
  have hxx0 : ‖x - x‖ ≤ η := by rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hp1, hp2⟩ := hr_perturb x c x c' hxL hxL (by linarith) (by linarith) hxx0 hccη
  have hLM : L * η ≤ M * η := mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) hη.le
  have hLLLM : L * L * L * η ≤ M * η :=
    mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) hη.le
  refine ⟨x, hxS, ?_, ?_⟩
  · linarith
  · linarith

end

end GroupApproximation.Full.TWWSchafhauser
