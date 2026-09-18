import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBusby

/-!
# Local compressions of a Busby lift: the cone of compressible maps

Lane `TWWSch3c2C2`, work order `WO-TWWSch-3c2-C2`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the absorption step of Schafhauser's proof
of the Tikuisis--White--Winter theorem. Sources: G. A. Elliott and D. Kucerovsky, Pacific J. Math.
198 (2001), Lemma 7 and the proof of Thm. 6; J. Gabe, *A note on nonunital absorbing extensions*,
Pacific J. Math. 284 (2016) (arXiv 1408.4033), for the unital case used here.

Let `ℓ : S → 𝓑(H_J)` be a map (in practice the bounded lift `x.bddLift` of a Busby cycle) and
`φ : S → 𝓑(H_J)` a target map. `φ` is **locally compressible into `ℓ`** when, for every finite
set `G ⊆ S`, every finite set `C` of compact operators and every `ε > 0`, there is a *compact*
`v` with `‖v⋆ ℓ(s) v − φ(s)‖ ≤ ε` for `s ∈ G` and `‖c⋆ v‖ ≤ ε` for `c ∈ C` ("`v` is pushed
past `C`"). This is the output of Elliott--Kucerovsky's Lemma 7, and the input of the
diagonal argument building an isometry that compresses `ℓ` onto a trivial extension.

This file proves the elementary closure properties of the class of such `φ`:

* `isLocallyCompressible_zero`, `IsLocallyCompressible.add`, `isLocallyCompressible_sum`: a cone.
  For sums the second compression is chosen orthogonal to `ℓ(s) v₁` and `ℓ(s)⋆ v₁`, which kills
  the cross terms.
* `IsLocallyCompressible.conj`: `s ↦ a⋆ φ(s) a` is compressible (use `v a`).
* `isLocallyCompressible_of_approx`: the class is closed under pointwise approximation on finite
  sets.
* `CompressesOn.norm_le`: when `ℓ(1) − 1` is compact, a compression that also sees `1` and
  `(ℓ(1) − 1)⋆` has `‖v‖ ≤ ‖φ(1)‖ + 2`.
* `IsLocallyCompressible.of_compact_perturb`: the class depends on `ℓ` only modulo compacts.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-! ## Compact elements of `𝓑(H_J)` -/

/-- `T ∈ 𝓑(H_J)` is **compact** (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def IsStdCompact (T : StdBdd J) : Prop := T.1.IsCompactOp

/-- `0` is compact (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem isStdCompact_zero : IsStdCompact (0 : StdBdd J) := by
  unfold IsStdCompact
  rw [StdBdd.coe_zero]
  exact Adjointable.isCompactOp_zero

/-- Compacts are closed under addition (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem IsStdCompact.add {T U : StdBdd J} (hT : IsStdCompact T) (hU : IsStdCompact U) :
    IsStdCompact (T + U) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_add]
  exact hT.add hU

/-- Compacts are closed under subtraction (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem IsStdCompact.sub {T U : StdBdd J} (hT : IsStdCompact T) (hU : IsStdCompact U) :
    IsStdCompact (T - U) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_sub]
  exact hT.sub hU

/-- Compacts form a left ideal (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsStdCompact.mul_left {v : StdBdd J} (hv : IsStdCompact v) (a : StdBdd J) :
    IsStdCompact (a * v) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_mul]
  exact hv.comp_left a.isBounded

/-- Compacts form a right ideal (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsStdCompact.mul_right {v : StdBdd J} (hv : IsStdCompact v) (a : StdBdd J) :
    IsStdCompact (v * a) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_mul]
  exact hv.comp_right a.isBounded

/-- Compacts are `⋆`-closed (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsStdCompact.star {v : StdBdd J} (hv : IsStdCompact v) : IsStdCompact (star v) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_star]
  exact hv.adjoint

/-- Compacts are closed under scalars (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem IsStdCompact.smul {v : StdBdd J} (hv : IsStdCompact v) (c : ℂ) :
    IsStdCompact (c • v) := by
  unfold IsStdCompact at *
  rw [StdBdd.coe_smul]
  exact hv.smul c

/-- A norm bound is an operator bound (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.isBoundedBy_of_norm_le {T : StdBdd J} {ε : ℝ} (h : ‖T‖ ≤ ε) :
    T.1.IsBoundedBy ε := by
  change T.1.opNorm ≤ ε at h
  exact (Adjointable.isBoundedBy_opNorm T.isBounded).mono h

/-- An operator bound is a norm bound (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_le_of_isBoundedBy {T : StdBdd J} {ε : ℝ} (hε : 0 ≤ ε)
    (h : T.1.IsBoundedBy ε) : ‖T‖ ≤ ε := by
  change T.1.opNorm ≤ ε
  exact Adjointable.opNorm_le_of_bound hε h

/-! ## Compressions -/

variable {S : Type*}

/-- `v` **compresses `ℓ` onto `φ` on `G` up to `ε`, past `C`**: `v` is compact,
`‖v⋆ ℓ(s) v − φ(s)‖ ≤ ε` for `s ∈ G` and `‖c⋆ v‖ ≤ ε` for `c ∈ C` (Elliott--Kucerovsky 2001,
Lemma 7; `non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def CompressesOn (ℓ φ : S → StdBdd J) (G : Finset S) (C : Finset (StdBdd J)) (ε : ℝ)
    (v : StdBdd J) : Prop :=
  IsStdCompact v ∧ (∀ s ∈ G, ‖star v * ℓ s * v - φ s‖ ≤ ε) ∧ ∀ c ∈ C, ‖star c * v‖ ≤ ε

/-- `φ` is **locally compressible into `ℓ`**: for all finite `G ⊆ S`, finite sets `C` of
compacts and `ε > 0` there is a compact compression (Elliott--Kucerovsky 2001, Lemma 7;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def IsLocallyCompressible (ℓ φ : S → StdBdd J) : Prop :=
  ∀ (G : Finset S) (C : Finset (StdBdd J)), (∀ c ∈ C, IsStdCompact c) →
    ∀ ε : ℝ, 0 < ε → ∃ v : StdBdd J, CompressesOn ℓ φ G C ε v

/-- The zero map is locally compressible (`v = 0`) (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem isLocallyCompressible_zero {ℓ : S → StdBdd J} :
    IsLocallyCompressible ℓ (fun _ => (0 : StdBdd J)) := by
  intro G C _ ε hε
  refine ⟨0, isStdCompact_zero, fun s _ => ?_, fun c _ => ?_⟩
  · simp only [mul_zero, sub_zero, norm_zero]
    exact hε.le
  · simp only [mul_zero, norm_zero]
    exact hε.le

/-- **Sums of compressible maps are compressible** (Elliott--Kucerovsky 2001, proof of Lemma 7):
compress `ψ` by `v₂` orthogonal to `ℓ(s) v₁` and `ℓ(s)⋆ v₁`, and take `v₁ + v₂`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsLocallyCompressible.add {ℓ φ ψ : S → StdBdd J} (hφ : IsLocallyCompressible ℓ φ)
    (hψ : IsLocallyCompressible ℓ ψ) : IsLocallyCompressible ℓ (fun s => φ s + ψ s) := by
  classical
  intro G C hC ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨v₁, hv₁, hG₁, hC₁⟩ := hφ G C hC (ε / 4) hδ
  have hC₂ : ∀ c ∈ C ∪ G.image (fun s => ℓ s * v₁) ∪ G.image (fun s => star (ℓ s) * v₁),
      IsStdCompact c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact hC c hc
      · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
        exact hv₁.mul_left (ℓ s)
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
      exact hv₁.mul_left (star (ℓ s))
  obtain ⟨v₂, hv₂, hG₂, hC₂'⟩ := hψ G _ hC₂ (ε / 4) hδ
  refine ⟨v₁ + v₂, hv₁.add hv₂, fun s hs => ?_, fun c hc => ?_⟩
  · have e1 : ‖star (star (ℓ s) * v₁) * v₂‖ ≤ ε / 4 :=
      hC₂' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun s => star (ℓ s) * v₁) hs))
    have e2 : ‖star (ℓ s * v₁) * v₂‖ ≤ ε / 4 :=
      hC₂' _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun s => ℓ s * v₁) hs)))
    have key : star (v₁ + v₂) * ℓ s * (v₁ + v₂) - (φ s + ψ s) =
        (star v₁ * ℓ s * v₁ - φ s) + (star v₂ * ℓ s * v₂ - ψ s) +
          star (star (ℓ s) * v₁) * v₂ + star (star (ℓ s * v₁) * v₂) := by
      simp only [star_add, star_mul, star_star]
      noncomm_ring
    rw [key]
    refine norm_add₄_le.trans ?_
    rw [norm_star]
    linarith [hG₁ s hs, hG₂ s hs]
  · have hc₂ : c ∈ C ∪ G.image (fun s => ℓ s * v₁) ∪ G.image (fun s => star (ℓ s) * v₁) :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hc)
    rw [mul_add]
    refine (norm_add_le _ _).trans ?_
    linarith [hC₁ c hc, hC₂' c hc₂]

/-- **Finite sums of compressible maps are compressible** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem isLocallyCompressible_sum {ι : Type*} (t : Finset ι) {ℓ : S → StdBdd J}
    {φ : ι → S → StdBdd J} (h : ∀ i ∈ t, IsLocallyCompressible ℓ (φ i)) :
    IsLocallyCompressible ℓ (fun s => ∑ i ∈ t, φ i s) := by
  classical
  revert h
  induction t using Finset.induction_on with
  | empty =>
    intro _
    have e : (fun s => ∑ i ∈ (∅ : Finset ι), φ i s) = fun _ => (0 : StdBdd J) := by
      funext s
      exact Finset.sum_empty
    rw [e]
    exact isLocallyCompressible_zero
  | insert i t hi ih =>
    intro h
    have e : (fun s => ∑ j ∈ insert i t, φ j s) = fun s => φ i s + ∑ j ∈ t, φ j s := by
      funext s
      exact Finset.sum_insert hi
    rw [e]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Conjugation**: if `φ` is compressible then so is `s ↦ a⋆ φ(s) a`, compressed by `v a`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsLocallyCompressible.conj {ℓ φ : S → StdBdd J} (hφ : IsLocallyCompressible ℓ φ)
    (a : StdBdd J) : IsLocallyCompressible ℓ (fun s => star a * φ s * a) := by
  intro G C hC ε hε
  have hM : 0 < (‖a‖ + 1) ^ 2 := by positivity
  have hδ : 0 < ε / (‖a‖ + 1) ^ 2 := div_pos hε hM
  obtain ⟨v, hv, hG, hCv⟩ := hφ G C hC (ε / (‖a‖ + 1) ^ 2) hδ
  have ha : ‖a‖ ≤ (‖a‖ + 1) ^ 2 := by nlinarith [norm_nonneg a]
  have ha2 : ‖a‖ * ‖a‖ ≤ (‖a‖ + 1) ^ 2 := by nlinarith [norm_nonneg a]
  have hcancel : (‖a‖ + 1) ^ 2 * (ε / (‖a‖ + 1) ^ 2) = ε := mul_div_cancel₀ ε hM.ne'
  refine ⟨v * a, hv.mul_right a, fun s hs => ?_, fun c hc => ?_⟩
  · have key : star (v * a) * ℓ s * (v * a) - star a * φ s * a =
        star a * (star v * ℓ s * v - φ s) * a := by
      rw [star_mul]
      noncomm_ring
    rw [key]
    calc ‖star a * (star v * ℓ s * v - φ s) * a‖
        ≤ ‖star a‖ * ‖star v * ℓ s * v - φ s‖ * ‖a‖ := norm_mul₃_le
      _ = ‖a‖ * ‖a‖ * ‖star v * ℓ s * v - φ s‖ := by rw [norm_star]; ring
      _ ≤ (‖a‖ + 1) ^ 2 * (ε / (‖a‖ + 1) ^ 2) :=
          mul_le_mul ha2 (hG s hs) (norm_nonneg _) hM.le
      _ = ε := hcancel
  · rw [← mul_assoc]
    calc ‖star c * v * a‖ ≤ ‖star c * v‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ ε / (‖a‖ + 1) ^ 2 * (‖a‖ + 1) ^ 2 :=
          mul_le_mul (hCv c hc) ha (norm_nonneg _) hδ.le
      _ = ε := by rw [mul_comm]; exact hcancel

/-- **Approximation**: a map approximable on finite sets by compressible maps is compressible
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem isLocallyCompressible_of_approx {ℓ φ : S → StdBdd J}
    (h : ∀ (G : Finset S) (ε : ℝ), 0 < ε → ∃ ψ : S → StdBdd J,
      IsLocallyCompressible ℓ ψ ∧ ∀ s ∈ G, ‖ψ s - φ s‖ ≤ ε) :
    IsLocallyCompressible ℓ φ := by
  intro G C hC ε hε
  obtain ⟨ψ, hψ, hψφ⟩ := h G (ε / 2) (half_pos hε)
  obtain ⟨v, hv, hG, hCv⟩ := hψ G C hC (ε / 2) (half_pos hε)
  refine ⟨v, hv, fun s hs => ?_, fun c hc => ?_⟩
  · have e : star v * ℓ s * v - φ s = (star v * ℓ s * v - ψ s) + (ψ s - φ s) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith [hG s hs, hψφ s hs]
  · linarith [hCv c hc]

/-! ## The norm bound and compact perturbations of the lift -/

/-- **Norm bound of a compression**: if `1 ∈ G`, `(ℓ(1) − 1)⋆ ∈ C` and `δ ≤ 1`, then
`‖v‖² ≤ ‖φ(1)‖ + δ + δ ‖v‖`, hence `‖v‖ ≤ ‖φ(1)‖ + 2` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem CompressesOn.norm_le [One S] {ℓ φ : S → StdBdd J} {G : Finset S}
    {C : Finset (StdBdd J)} {δ : ℝ} {v : StdBdd J} (hv : CompressesOn ℓ φ G C δ v)
    (hδ : δ ≤ 1) (h1 : (1 : S) ∈ G) (hc : star (ℓ 1 - 1) ∈ C) : ‖v‖ ≤ ‖φ 1‖ + 2 := by
  obtain ⟨_, hG, hC⟩ := hv
  have e1 := hG 1 h1
  have e2 : ‖star (star (ℓ 1 - 1)) * v‖ ≤ δ := hC _ hc
  rw [star_star] at e2
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans e1
  have key : star v * v = (star v * ℓ 1 * v - φ 1) + φ 1 - star v * ((ℓ 1 - 1) * v) := by
    noncomm_ring
  have hvv : ‖v‖ * ‖v‖ ≤ δ + ‖φ 1‖ + ‖v‖ * δ := by
    rw [← CStarRing.norm_star_mul_self, key]
    have t1 := norm_sub_le (star v * ℓ 1 * v - φ 1 + φ 1) (star v * ((ℓ 1 - 1) * v))
    have t2 := norm_add_le (star v * ℓ 1 * v - φ 1) (φ 1)
    have t3 := norm_mul_le (star v) ((ℓ 1 - 1) * v)
    rw [norm_star] at t3
    have t4 := mul_le_mul_of_nonneg_left e2 (norm_nonneg v)
    linarith
  have hv' : ‖v‖ * ‖v‖ ≤ 1 + ‖φ 1‖ + ‖v‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (norm_nonneg v)]
  by_contra hlt
  push Not at hlt
  have ht : 0 < ‖v‖ := by linarith [norm_nonneg (φ 1)]
  nlinarith [mul_lt_mul_of_pos_right hlt ht,
    mul_nonneg (norm_nonneg (φ 1)) (by linarith : (0 : ℝ) ≤ ‖v‖ - 2)]

/-- **Compact perturbations of the lift**: if `ℓ(1) − 1` is compact and `ℓ' − ℓ` is pointwise
compact, every map compressible into `ℓ` is compressible into `ℓ'`. The error
`v⋆ (ℓ' − ℓ)(s) v = ((ℓ' − ℓ)(s)⋆ v)⋆ v` is controlled by orthogonality and
`CompressesOn.norm_le` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsLocallyCompressible.of_compact_perturb [One S] {ℓ ℓ' φ : S → StdBdd J}
    (h : IsLocallyCompressible ℓ φ) (h1 : IsStdCompact (ℓ 1 - 1))
    (hℓ : ∀ s, IsStdCompact (ℓ' s - ℓ s)) : IsLocallyCompressible ℓ' φ := by
  classical
  intro G C hC ε hε
  have hA : 0 < ‖φ 1‖ + 3 := by linarith [norm_nonneg (φ 1)]
  set δ : ℝ := min 1 (ε / (‖φ 1‖ + 3))
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε hA)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (‖φ 1‖ + 3) ≤ ε :=
    calc δ * (‖φ 1‖ + 3) ≤ ε / (‖φ 1‖ + 3) * (‖φ 1‖ + 3) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
      _ = ε := div_mul_cancel₀ ε hA.ne'
  have hC' : ∀ c ∈ C ∪ {star (ℓ 1 - 1)} ∪ G.image (fun s => ℓ' s - ℓ s), IsStdCompact c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact hC c hc
      · rw [Finset.mem_singleton.mp hc]
        exact h1.star
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
      exact hℓ s
  obtain ⟨v, hv⟩ := h (insert 1 G) _ hC' δ hδ0
  have hnorm : ‖v‖ ≤ ‖φ 1‖ + 2 := hv.norm_le hδ1 (Finset.mem_insert_self 1 G)
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  obtain ⟨hvc, hG, hCv⟩ := hv
  refine ⟨v, hvc, fun s hs => ?_, fun c hc => ?_⟩
  · have ek : ‖star (ℓ' s - ℓ s) * v‖ ≤ δ :=
      hCv _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun s => ℓ' s - ℓ s) hs))
    have key : star v * ℓ' s * v - φ s =
        (star v * ℓ s * v - φ s) + star (star (ℓ' s - ℓ s) * v) * v := by
      simp only [star_mul, star_star]
      noncomm_ring
    rw [key]
    have t1 := norm_add_le (star v * ℓ s * v - φ s) (star (star (ℓ' s - ℓ s) * v) * v)
    have t2 := norm_mul_le (star (star (ℓ' s - ℓ s) * v)) v
    rw [norm_star] at t2
    have t3 := mul_le_mul ek hnorm (norm_nonneg v) hδ0.le
    have t4 := hG s (Finset.mem_insert_of_mem hs)
    nlinarith
  · have hc' : c ∈ C ∪ {star (ℓ 1 - 1)} ∪ G.image (fun s => ℓ' s - ℓ s) :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hc)
    have := hCv c hc'
    nlinarith [mul_nonneg hδ0.le (norm_nonneg (φ 1))]

end

end GroupApproximation.Full.TWWSchafhauser
