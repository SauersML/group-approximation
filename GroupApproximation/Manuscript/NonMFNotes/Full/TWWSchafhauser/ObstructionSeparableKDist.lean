import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSeparable
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosArvesonPairQuotient

/-!
# Separable inheritance, step 0: distances to `D ∩ J`

Lane `TWWSch3d2S`, work order `WO-TWWSch-3d2-S`.
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), Lemma 4.4. The separable reduction there
(B. Blackadar, *Operator Algebras*, II.8.5) needs `K₁(D ∩ J) = 0` and `K₀(D ∩ J)` divisible
along an increasing chain of separable subalgebras `D`. The perturbation arguments for that
start from the fact proved here.

For a closed subalgebra `D` of `B` and a closed ideal `J`, the map `D ⧸ (D ∩ J) → B ⧸ J` is an
injective ⋆-homomorphism of C⋆-algebras, hence isometric. So an element `d ∈ D` that is close
to `J` is equally close to `D ∩ J`.

* `jIdeal J hideal`: the closed star subalgebra `J` as a two-sided ideal of `B`;
* `exists_mem_sepIdeal_near`: if `d ∈ D` and `x ∈ J` have `‖d - x‖ < ε`, then some
  `y ∈ D ∩ J` has `‖d - y‖ < ε`;
* `exists_mem_sepIdeal_chain_near`: `⋃ₖ (Dₖ ∩ J)` is dense in `chainClosure D ∩ J`;
* `exists_sepIdeal_chain_near_fintype`: the same for finitely many elements at a common
  stage `k`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

variable {B : Type} [CStarAlgebra B]

/-! ### `J` as an ideal -/

/-- The star subalgebra `J`, closed under multiplication by `B` on both sides, as a two-sided
ideal of `B`. -/
def jIdeal (J : NonUnitalStarSubalgebra ℂ B)
    (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J) : Ideal B where
  carrier := J
  add_mem' := by
    intro a b ha hb
    exact SetLike.mem_coe.mpr (add_mem (SetLike.mem_coe.mp ha) (SetLike.mem_coe.mp hb))
  zero_mem' := SetLike.mem_coe.mpr (zero_mem J)
  smul_mem' := by
    intro b x hx
    exact SetLike.mem_coe.mpr (hideal b x (SetLike.mem_coe.mp hx)).1

section Ideal

variable (J : NonUnitalStarSubalgebra ℂ B) (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J)

theorem mem_jIdeal {x : B} : x ∈ jIdeal J hideal ↔ x ∈ J :=
  Iff.rfl

instance jIdeal_isTwoSided : (jIdeal J hideal).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    exact (mem_jIdeal J hideal).mpr (hideal b a ((mem_jIdeal J hideal).mp ha)).2

instance jIdeal_isStarStable : CStarTensor.IsStarStable (jIdeal J hideal) where
  star_mem := by
    intro a ha
    exact (mem_jIdeal J hideal).mpr (star_mem ((mem_jIdeal J hideal).mp ha))

instance jIdeal_isClosed [hJ : IsClosed (J : Set B)] :
    IsClosed ((jIdeal J hideal : Ideal B) : Set B) :=
  hJ

end Ideal

/-! ### The distance to `D ∩ J` -/

/-- The sets `D ∩ J` grow with `D`. -/
theorem sepIdeal_mono {J : NonUnitalStarSubalgebra ℂ B} {D D' : StarSubalgebra ℂ B}
    (h : D ≤ D') : sepIdeal D J ≤ sepIdeal D' J := by
  intro x hx
  exact mem_sepIdeal.mpr ⟨h (mem_sepIdeal.mp hx).1, (mem_sepIdeal.mp hx).2⟩

/-- **Distances to `D ∩ J` equal distances to `J`** (Schafhauser 2020, proof of Lemma 4.4;
Blackadar II.5.1.1). If `d ∈ D` lies within `ε` of `J`, it lies within `ε` of `D ∩ J`.
The factored map `D ⧸ (D ∩ J) → B ⧸ J` is an injective ⋆-homomorphism, hence isometric
(`arvesonKernel_exists_near` applied to `D → B ⧸ J`). -/
theorem exists_mem_sepIdeal_near {J : NonUnitalStarSubalgebra ℂ B} (hJ : IsClosed (J : Set B))
    (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J) {D : StarSubalgebra ℂ B}
    (hD : IsClosed (D : Set B)) {d x : B} (hd : d ∈ D) (hx : x ∈ J) {ε : ℝ}
    (hdx : ‖d - x‖ < ε) : ∃ y ∈ sepIdeal D J, ‖d - y‖ < ε := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨0, zero_mem _, ?_⟩
    have h0 : d - 0 = d - x := Subsingleton.elim _ _
    rw [h0]
    exact hdx
  haveI : IsClosed (J : Set B) := hJ
  haveI : IsClosed (D : Set B) := hD
  haveI : Nontrivial D := ⟨⟨0, 1, fun h => zero_ne_one (α := B) (congrArg Subtype.val h)⟩⟩
  have hπd : ‖((CStarTensor.quotientStarMk (jIdeal J hideal)).comp D.subtype) ⟨d, hd⟩‖ ≤
      ‖d - x‖ := by
    have hx0 : Ideal.Quotient.mk (jIdeal J hideal) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_jIdeal J hideal).mpr hx)
    have h1 : ((CStarTensor.quotientStarMk (jIdeal J hideal)).comp D.subtype) ⟨d, hd⟩ =
        Ideal.Quotient.mk (jIdeal J hideal) (d - x) := by
      rw [map_sub, hx0, sub_zero]
      rfl
    rw [h1]
    exact CStarTensor.quotient_norm_mk_le (jIdeal J hideal) (d - x)
  obtain ⟨j, hj, hjn⟩ := arvesonKernel_exists_near
    ((CStarTensor.quotientStarMk (jIdeal J hideal)).comp D.subtype) ⟨d, hd⟩
    (sub_pos.mpr (hπd.trans_lt hdx))
  refine ⟨(j : B), mem_sepIdeal.mpr ⟨j.2, ?_⟩, ?_⟩
  · have hj0 : Ideal.Quotient.mk (jIdeal J hideal) (j : B) = 0 :=
      (mem_arvesonKernel_iff _ j).mp hj
    exact (mem_jIdeal J hideal).mp (Ideal.Quotient.eq_zero_iff_mem.mp hj0)
  · have hnorm : ‖(⟨d, hd⟩ : D) - j‖ = ‖d - (j : B)‖ := rfl
    rw [← hnorm]
    linarith

/-- **`⋃ₖ (Dₖ ∩ J)` is dense in `chainClosure D ∩ J`.** Approximate `x` by `d ∈ Dₖ`; then `d`
is close to `J`, hence to `Dₖ ∩ J` by `exists_mem_sepIdeal_near`. -/
theorem exists_mem_sepIdeal_chain_near {J : NonUnitalStarSubalgebra ℂ B}
    (hJ : IsClosed (J : Set B)) (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J)
    {D : ℕ → StarSubalgebra ℂ B} (hmono : Monotone D) (hD : ∀ n, IsClosed (D n : Set B))
    {x : B} (hx : x ∈ sepIdeal (chainClosure D) J) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ∃ y ∈ sepIdeal (D k) J, ‖x - y‖ < ε := by
  obtain ⟨hxD, hxJ⟩ := mem_sepIdeal.mp hx
  have hcl : x ∈ closure (⋃ n, (D n : Set B)) := by
    have h : x ∈ ((⨆ n, D n).topologicalClosure : Set B) := hxD
    rwa [StarSubalgebra.topologicalClosure_coe,
      StarSubalgebra.coe_iSup_of_directed hmono.directed_le] at h
  obtain ⟨d, hdU, hdx⟩ := Metric.mem_closure_iff.mp hcl (ε / 2) (half_pos hε)
  obtain ⟨k, hdk⟩ := Set.mem_iUnion.mp hdU
  have hxd : ‖x - d‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hdx
  have hdx' : ‖d - x‖ < ε / 2 := by
    rw [norm_sub_rev]
    exact hxd
  obtain ⟨y, hy, hyd⟩ := exists_mem_sepIdeal_near hJ hideal (hD k) hdk hxJ hdx'
  refine ⟨k, y, hy, ?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub x d y
  linarith

/-- The density of `exists_mem_sepIdeal_chain_near`, for finitely many elements at once and at
a common stage `k`. -/
theorem exists_sepIdeal_chain_near_fintype {J : NonUnitalStarSubalgebra ℂ B}
    (hJ : IsClosed (J : Set B)) (hideal : ∀ b x, x ∈ J → b * x ∈ J ∧ x * b ∈ J)
    {D : ℕ → StarSubalgebra ℂ B} (hmono : Monotone D) (hD : ∀ n, IsClosed (D n : Set B))
    {ι : Type*} [Fintype ι] (x : ι → B) (hx : ∀ i, x i ∈ sepIdeal (chainClosure D) J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ∃ y : ι → B, (∀ i, y i ∈ sepIdeal (D k) J) ∧ ∀ i, ‖x i - y i‖ < ε := by
  choose k y hy hxy using fun i => exists_mem_sepIdeal_chain_near hJ hideal hmono hD (hx i) hε
  refine ⟨Finset.univ.sup k, y, fun i => ?_, hxy⟩
  exact sepIdeal_mono (hmono (Finset.le_sup (Finset.mem_univ i))) (hy i)

end

end GroupApproximation.Full.TWWSchafhauser
