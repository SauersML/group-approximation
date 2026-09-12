import GroupApproximation.KOne.AryGradedComponents
import GroupApproximation.KOne.AryRankNormalForm
import GroupApproximation.KOne.AryCylinderCornerRank
import GroupApproximation.KOne.AryNilpotentTailKill
import GroupApproximation.Meta.AxiomGuard

/-!
# The keystone at arbitrary arity: balanced parts of `[0,1]`-window units are invertible

`KOne/ZeroKOne.lean` for `L_k(1,d)`.  If `c + ζ` is a unit with `c` balanced and `ζ` of
pure degree `1`, then `c` is invertible.  Otherwise the rank normal form turns the unit
into `e + ζ'` with `e` a proper cylinder-sum idempotent and `f := 1 - e` a nonempty
cylinder sum; the graded components of the inverse satisfy a two-term recursion whose
downward elimination gives `f = Σ_j (f·ζ'·(-ζ')^j)·(f·(y_{-1-j}·f))`, and at a deep
interface the right side factors through spaces of geometrically decaying dimension:
`|T|·d^{ℓ-n} ≤ Σ_{j<M} |T|·d^{ℓ-n-1-j} < |T|·d^{ℓ-n}`, impossible.  The binary file has
`2` where this has `d`; the geometric bound only needs `d ≥ 2`.
-/

namespace GroupApproximation
namespace AryLeavitt

open CompleteMatrixFamily

variable (k : Type) [Field k] (d : ℕ)

/-- Geometric sums of powers are below the next power. -/
theorem sum_pow_lt_pow {b : ℕ} (hb : 2 ≤ b) : ∀ m : ℕ, ∑ i ∈ Finset.range m, b ^ i < b ^ m
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ, pow_succ]
      have ih := sum_pow_lt_pow hb m
      have h2 : b ^ m * 2 ≤ b ^ m * b := Nat.mul_le_mul_left (b ^ m) hb
      omega

/-- **Balanced parts of `[0,1]`-window units are invertible.** -/
theorem balanced_component_isUnit (hd : 2 ≤ d) {c ζ : AryLeavittAlgebra k d}
    (hc : c ∈ Submodule.span k ((family k d).degreeMonomials 0 0))
    (hζ : ζ ∈ Submodule.span k ((family k d).degreeMonomials 1 1))
    (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) = c + ζ) : IsUnit c := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  by_contra hcu
  set F : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) := family k d with hF
  have hb : 2 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
  -- rank-normalize the balanced part
  obtain ⟨n, hcn⟩ := F.span_degree_zero_le_levelSpan (k := k) hc
  obtain ⟨g, h, S, hgv, hgi, hhv, hhi, hgch, hSU⟩ := F.exists_rank_normal_form hcn
  have hSne : S ≠ Finset.univ := fun hS ↦ hcu (hSU hS)
  set T : Finset (Fin n → Fin d) := Finset.univ \ S with hT
  have hTpos : 0 < T.card := by
    refine Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr ?_)
    intro hsub
    exact hSne (Finset.univ_subset_iff.mp hsub)
  set e : AryLeavittAlgebra k d := ∑ γ ∈ S, F.cylinder (List.ofFn γ) with he
  set f : AryLeavittAlgebra k d := ∑ γ ∈ T, F.cylinder (List.ofFn γ) with hf
  have hef : e + f = 1 := by
    rw [he, hf, hT, add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
    exact F.sum_cylinder_ofFn n
  have hcyl : ∀ γ δ : Fin n → Fin d,
      F.cylinder (List.ofFn γ) * F.cylinder (List.ofFn δ) =
        if γ = δ then F.cylinder (List.ofFn γ) else 0 := by
    intro γ δ
    unfold cylinder
    rw [show F.wordS (List.ofFn γ) * F.wordT (List.ofFn γ) *
        (F.wordS (List.ofFn δ) * F.wordT (List.ofFn δ)) =
      F.wordS (List.ofFn γ) * (F.wordT (List.ofFn γ) * F.wordS (List.ofFn δ)) *
        F.wordT (List.ofFn δ) from by noncomm_ring,
      F.powerFamily_orthogonal n γ δ]
    by_cases hγδ : γ = δ
    · rw [if_pos hγδ, if_pos hγδ, mul_one, hγδ]
    · rw [if_neg hγδ, if_neg hγδ]
      noncomm_ring
  have hfe : f * e = 0 := by
    rw [hf, he, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun γ hγ ↦ Finset.sum_eq_zero fun δ hδ ↦ ?_
    rw [hcyl γ δ, if_neg ?_]
    rintro rfl
    rw [hT] at hγ
    exact (Finset.mem_sdiff.mp hγ).2 hδ
  have hff : f * f = f := by
    rw [hf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun γ hγ ↦ ?_
    rw [Finset.sum_eq_single γ]
    · rw [hcyl γ γ, if_pos rfl]
    · intro δ _ hδ
      rw [hcyl γ δ, if_neg (Ne.symm hδ)]
    · intro hγ'
      exact absurd hγ hγ'
  -- the normalized unit
  set w : (AryLeavittAlgebra k d)ˣ := g * u * h with hw
  set ζ' : AryLeavittAlgebra k d :=
    (g : AryLeavittAlgebra k d) * ζ * (h : AryLeavittAlgebra k d) with hζ'def
  have hwv : (w : AryLeavittAlgebra k d) = e + ζ' := by
    rw [hw]
    show (g : AryLeavittAlgebra k d) * (u : AryLeavittAlgebra k d) *
      (h : AryLeavittAlgebra k d) = e + ζ'
    rw [hu, show (g : AryLeavittAlgebra k d) * (c + ζ) * (h : AryLeavittAlgebra k d) =
      (g : AryLeavittAlgebra k d) * c * (h : AryLeavittAlgebra k d) +
        (g : AryLeavittAlgebra k d) * ζ * (h : AryLeavittAlgebra k d) from by noncomm_ring,
      hgch, hζ'def, he]
  -- degree memberships
  have hgd : (g : AryLeavittAlgebra k d) ∈ Submodule.span k (F.degreeMonomials 0 0) :=
    F.span_levelMonomialSet_le_degree (k := k) n hgv
  have hhd : (h : AryLeavittAlgebra k d) ∈ Submodule.span k (F.degreeMonomials 0 0) :=
    F.span_levelMonomialSet_le_degree (k := k) n hhv
  have hζ'd : ζ' ∈ Submodule.span k (F.degreeMonomials 1 1) := by
    rw [hζ'def]
    have h1 := F.window_mul_mem_span (k := k) (F.window_mul_mem_span (k := k) hgd hζ) hhd
    refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hed : e ∈ Submodule.span k (F.degreeMonomials 0 0) := by
    rw [he]
    exact Submodule.sum_mem _ fun γ _ ↦ Submodule.subset_span
      ⟨List.ofFn γ, List.ofFn γ, by simp, by simp, rfl⟩
  -- graded components of the inverse
  obtain ⟨lo₀, hi₀, hx₀⟩ := exists_mem_span_degreeMonomials k d
    ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
  set lo : ℤ := min lo₀ (-1) with hlo
  set hi : ℤ := max hi₀ 0 with hhi
  have hlo1 : lo ≤ -1 := min_le_right _ _
  have hhi1 : (0 : ℤ) ≤ hi := le_max_right _ _
  have hx : ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k (F.degreeMonomials lo hi) :=
    F.span_degreeMonomials_mono (min_le_left _ _) (le_max_left _ _) hx₀
  obtain ⟨y, hymem, hysupp, hysum⟩ := F.exists_components hx
  set D : Finset ℤ := Finset.Icc lo (hi + 1) with hD
  have h0D : (0 : ℤ) ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hzmem : ∀ j ∈ D, e * y j + ζ' * y (j - 1) ∈
      Submodule.span k (F.degreeMonomials j j) := by
    intro j _
    refine Submodule.add_mem _ ?_ ?_
    · have := F.window_mul_mem_span (k := k) hed (hymem j)
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> omega
    · have := F.window_mul_mem_span (k := k) hζ'd (hymem (j - 1))
      refine F.span_degreeMonomials_mono ?_ ?_ this <;> omega
  have hz'mem : ∀ j ∈ D, (if j = 0 then (1 : AryLeavittAlgebra k d) else 0) ∈
      Submodule.span k (F.degreeMonomials j j) := by
    intro j _
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact Submodule.subset_span ⟨[], [], by simp [hj], by simp [hj], by simp⟩
    · rw [if_neg hj]
      exact Submodule.zero_mem _
  have hshift : ∑ j ∈ D, y (j - 1) =
      ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
    have hmap : D = Finset.map (addRightEmbedding (1 : ℤ)) (Finset.Icc (lo - 1) hi) := by
      rw [Finset.map_add_right_Icc, show lo - 1 + 1 = lo from by ring]
    rw [hmap, Finset.sum_map]
    have hstep : ∀ j ∈ Finset.Icc (lo - 1) hi,
        y (addRightEmbedding (1 : ℤ) j - 1) = y j := by
      intro j _
      congr 1
      simp [addRightEmbedding]
    rw [Finset.sum_congr rfl hstep]
    have hins : Finset.Icc (lo - 1) hi = insert (lo - 1) (Finset.Icc lo hi) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      hysupp (lo - 1) (Or.inl (by omega)), zero_add, hysum]
  have hplain : ∑ j ∈ D, y j =
      ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
    have hins : D = insert (hi + 1) (Finset.Icc lo hi) := by
      ext j
      simp only [hD, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      hysupp (hi + 1) (Or.inr (by omega)), zero_add, hysum]
  have hsum1 : ∑ j ∈ D, (e * y j + ζ' * y (j - 1)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hplain, hshift]
    calc e * ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) +
          ζ' * ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
        = (e + ζ') * ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
          noncomm_ring
      _ = (w : AryLeavittAlgebra k d) *
          ((w⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by rw [hwv]
      _ = 1 := w.mul_inv
  have hsum2 : ∑ j ∈ D, (if j = 0 then (1 : AryLeavittAlgebra k d) else 0) = 1 := by
    rw [Finset.sum_ite_eq' D (0 : ℤ) (fun _ ↦ (1 : AryLeavittAlgebra k d)), if_pos h0D]
  have heq := components_unique k d hd hzmem hz'mem (hsum1.trans hsum2.symm)
  -- the substitution identity for negative degrees
  have hsubst : ∀ j : ℤ, j ≤ -1 → y j = f * y j - ζ' * y (j - 1) := by
    intro j hj
    by_cases hjD : j ∈ D
    · have h1 := heq j hjD
      rw [if_neg (by omega)] at h1
      have h2 : e * y j = -(ζ' * y (j - 1)) := add_eq_zero_iff_eq_neg.mp h1
      calc y j = (e + f) * y j := by rw [hef, one_mul]
        _ = e * y j + f * y j := by noncomm_ring
        _ = f * y j - ζ' * y (j - 1) := by
            rw [h2]
            noncomm_ring
    · have h0 : y j = 0 := hysupp j (by
        rw [hD] at hjD
        simp only [Finset.mem_Icc] at hjD
        omega)
      have h0' : y (j - 1) = 0 := hysupp (j - 1) (by
        rw [hD] at hjD
        simp only [Finset.mem_Icc] at hjD
        omega)
      rw [h0, h0', mul_zero, mul_zero, sub_zero]
  -- the remainder induction
  set GG : ℕ → AryLeavittAlgebra k d := fun j ↦ f * ζ' * (-ζ') ^ j with hGG
  set YY : ℕ → AryLeavittAlgebra k d := fun j ↦ f * (y (-1 - (j : ℤ)) * f) with hYY
  have hclaim : ∀ m : ℕ, f = (∑ j ∈ Finset.range m, GG j * YY j) +
      f * ζ' * (-ζ') ^ m * y (-1 - (m : ℤ)) * f := by
    intro m
    induction m with
    | zero =>
        have h1 := heq 0 h0D
        rw [if_pos rfl] at h1
        have h2 := congrArg (fun z ↦ f * z * f) h1
        rw [show f * (e * y 0 + ζ' * y (0 - 1)) * f =
            (f * e) * (y 0 * f) + f * ζ' * y (0 - 1) * f from by noncomm_ring,
          hfe, zero_mul, zero_add, mul_one, hff] at h2
        rw [Finset.sum_range_zero, zero_add, pow_zero, mul_one]
        rw [show (-1 - ((0 : ℕ) : ℤ)) = 0 - 1 from by omega]
        exact h2.symm
    | succ m ih =>
        refine ih.trans ?_
        rw [Finset.sum_range_succ]
        have hexp := hsubst (-1 - (m : ℤ)) (by omega)
        have h3 := congrArg (fun z ↦ f * ζ' * (-ζ') ^ m * z * f) hexp
        have hpow0 : (-ζ') ^ (m + 1) + (-ζ') ^ m * ζ' = 0 := by
          rw [pow_succ, ← mul_add, neg_add_cancel, mul_zero]
        have hzero : f * ζ' * (-ζ') ^ (m + 1) * y (-1 - ((m + 1 : ℕ) : ℤ)) * f +
            f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f = 0 := by
          rw [show (-1 - ((m + 1 : ℕ) : ℤ)) = -1 - (m : ℤ) - 1 from by omega]
          calc f * ζ' * (-ζ') ^ (m + 1) * y (-1 - (m : ℤ) - 1) * f +
                f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f
              = f * ζ' * ((-ζ') ^ (m + 1) + (-ζ') ^ m * ζ') *
                  y (-1 - (m : ℤ) - 1) * f := by noncomm_ring
            _ = 0 := by rw [hpow0, mul_zero, zero_mul, zero_mul]
        have hrem : f * ζ' * (-ζ') ^ (m + 1) * y (-1 - ((m + 1 : ℕ) : ℤ)) * f =
            -(f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f) :=
          eq_neg_of_add_eq_zero_left hzero
        have hstep : f * ζ' * (-ζ') ^ m * y (-1 - (m : ℤ)) * f =
            GG m * YY m - f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f := by
          rw [h3]
          simp only [hGG, hYY]
          rw [mul_sub, sub_mul]
          congr 1
          noncomm_ring
        rw [hstep, hrem]
        abel
  -- termination of the expansion
  set M : ℕ := (-lo).toNat with hM
  have hstar : f = ∑ j ∈ Finset.range M, GG j * YY j := by
    have h1 := hclaim M
    rw [hysupp (-1 - (M : ℤ)) (Or.inl (by omega)), mul_zero, zero_mul, add_zero] at h1
    exact h1
  -- degree memberships of the corner factors
  have hfd : f ∈ Submodule.span k (F.degreeMonomials 0 0) := by
    rw [hf]
    exact Submodule.sum_mem _ fun γ _ ↦ Submodule.subset_span
      ⟨List.ofFn γ, List.ofFn γ, by simp, by simp, rfl⟩
  have hGGd : ∀ j : ℕ, GG j ∈
      Submodule.span k (F.degreeMonomials ((j : ℤ) + 1) ((j : ℤ) + 1)) := by
    intro j
    rw [hGG]
    have hpow : (-ζ') ^ j ∈ Submodule.span k (F.degreeMonomials (j : ℤ) (j : ℤ)) :=
      F.pow_mem_window (Submodule.neg_mem _ hζ'd) j
    have h1 := F.window_mul_mem_span (k := k) (F.window_mul_mem_span (k := k) hfd hζ'd) hpow
    refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  -- choose a deep uniform interface
  have hGsh : ∀ j : ℕ, ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q →
      (p : ℤ) = (q : ℤ) + ((j : ℤ) + 1) →
      GG j ∈ Submodule.span k (F.shapeMonomials p q) :=
    fun j ↦ F.exists_shapeSpan_of_degreeSpan (hGGd j)
  have hRsh : ∀ j : ℕ, ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q →
      (p : ℤ) = (q : ℤ) + (-1 - (j : ℤ)) →
      y (-1 - (j : ℤ)) * f ∈ Submodule.span k (F.shapeMonomials p q) := by
    intro j
    refine F.exists_shapeSpan_of_degreeSpan ?_
    have h1 := F.window_mul_mem_span (k := k) (hymem (-1 - (j : ℤ))) hfd
    refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  choose nG hnG using hGsh
  choose nR hnR using hRsh
  set B : ℕ := (Finset.range M).sup fun j ↦ max (nG j) (nR j) with hB
  set ℓ : ℕ := n + M + 1 + B with hℓ
  set K : ℕ := ℓ - n - 1 with hK
  have hKM : M ≤ K := by omega
  -- shape representations at the uniform interface
  have hreps : ∀ j ∈ Finset.range M, ∃
      (MG : Matrix (Fin ℓ → Fin d) (Fin (ℓ - 1 - j) → Fin d) k)
      (Mf : Matrix (Fin (ℓ - 1 - j) → Fin d) (Fin (ℓ - 1 - j) → Fin d) k)
      (Mr : Matrix (Fin (ℓ - 1 - j) → Fin d) (Fin ℓ → Fin d) k),
      F.ShapeRep ℓ ℓ (MG * (Mf * Mr)) (GG j * YY j) ∧
      F.ShapeRep (ℓ - 1 - j) (ℓ - 1 - j) Mf f := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hjB : max (nG j) (nR j) ≤ B := Finset.le_sup (f := fun j ↦ max (nG j) (nR j)) hj
    have hq : n ≤ ℓ - 1 - j := by omega
    have hGmem : GG j ∈ Submodule.span k (F.shapeMonomials ℓ (ℓ - 1 - j)) := by
      refine hnG j ℓ (ℓ - 1 - j) (by omega) ?_
      omega
    have hfmem : f ∈ Submodule.span k (F.shapeMonomials (ℓ - 1 - j) (ℓ - 1 - j)) := by
      rw [hf]
      exact F.cylSum_mem_shapeSpan T hq
    have hrmem : y (-1 - (j : ℤ)) * f ∈ Submodule.span k (F.shapeMonomials (ℓ - 1 - j) ℓ) := by
      refine hnR j (ℓ - 1 - j) ℓ (by omega) ?_
      omega
    obtain ⟨MG, hMG⟩ := F.exists_shapeRep hGmem
    obtain ⟨Mf, hMf⟩ := F.exists_shapeRep hfmem
    obtain ⟨Mr, hMr⟩ := F.exists_shapeRep hrmem
    refine ⟨MG, Mf, Mr, ?_, hMf⟩
    have hYrep : F.ShapeRep (ℓ - 1 - j) ℓ (Mf * Mr) (YY j) := by
      rw [hYY]
      exact F.shapeRep_mul hMf hMr
    exact F.shapeRep_mul hMG hYrep
  choose MG Mf Mr hprod hMfrep using hreps
  set Mtot : Matrix (Fin ℓ → Fin d) (Fin ℓ → Fin d) k :=
    ∑ j ∈ (Finset.range M).attach, MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2) with hMtot
  have hMtotrep : F.ShapeRep ℓ ℓ Mtot f := by
    rw [hstar, hMtot]
    have hsum := F.shapeRep_finsetSum (Finset.range M).attach
      (fun j ↦ MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2)) (fun j ↦ GG j.1 * YY j.1)
      (fun j _ ↦ hprod j.1 j.2)
    rwa [Finset.sum_attach (Finset.range M) (fun j ↦ GG j * YY j)] at hsum
  -- rank bounds
  set b : ℕ := Fintype.card (Fin d) with hbdef
  have hlower : T.card * b ^ (ℓ - n) ≤ Mtot.rank := by
    refine F.card_le_rank_of_shapeRep_cylSum T (by omega) ?_
    rw [← hf]
    exact hMtotrep
  have hupper : Mtot.rank ≤ ∑ j ∈ (Finset.range M).attach, T.card * b ^ (ℓ - 1 - j.1 - n) := by
    rw [hMtot]
    refine le_trans (rank_finsetSum_le _ _) ?_
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have h1 : (MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2)).rank ≤ (Mf j.1 j.2 * Mr j.1 j.2).rank :=
      Matrix.rank_mul_le_right _ _
    have h2 : (Mf j.1 j.2 * Mr j.1 j.2).rank ≤ (Mf j.1 j.2).rank :=
      Matrix.rank_mul_le_left _ _
    have h3 : (Mf j.1 j.2).rank ≤ T.card * b ^ (ℓ - 1 - j.1 - n) := by
      refine F.rank_le_card_of_shapeRep_cylSum T (by
        have := Finset.mem_range.mp j.2
        omega) ?_
      rw [← hf]
      exact hMfrep j.1 j.2
    exact le_trans h1 (le_trans h2 h3)
  -- the numerical contradiction
  have hgeom : ∑ j ∈ (Finset.range M).attach, T.card * b ^ (ℓ - 1 - j.1 - n) <
      T.card * b ^ (ℓ - n) := by
    rw [Finset.sum_attach (Finset.range M) (fun j ↦ T.card * b ^ (ℓ - 1 - j - n))]
    have hexp : ∀ j ∈ Finset.range M, T.card * b ^ (ℓ - 1 - j - n) = T.card * b ^ (K - j) := by
      intro j hj
      have := Finset.mem_range.mp hj
      congr 2
      omega
    rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum]
    have hrefl : ∑ j ∈ Finset.range M, b ^ (K - j) =
        ∑ i ∈ Finset.range M, b ^ (K - M + 1 + i) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have := Finset.mem_range.mp hi
      congr 1
      omega
    rw [hrefl]
    have hfact : ∑ i ∈ Finset.range M, b ^ (K - M + 1 + i) =
        b ^ (K - M + 1) * ∑ i ∈ Finset.range M, b ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]
    rw [hfact]
    have hgs := sum_pow_lt_pow hb M
    have hKn : b ^ (K - M + 1) * b ^ M = b ^ (ℓ - n) := by
      rw [← pow_add]
      congr 1
      omega
    have hbpos : 0 < b ^ (K - M + 1) := pow_pos (by omega) _
    calc T.card * (b ^ (K - M + 1) * ∑ i ∈ Finset.range M, b ^ i)
        < T.card * (b ^ (K - M + 1) * b ^ M) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hgs hbpos) hTpos
      _ = T.card * b ^ (ℓ - n) := by rw [hKn]
  exact absurd (lt_of_le_of_lt (hlower.trans hupper) hgeom) (lt_irrefl _)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.sum_pow_lt_pow
#audit_axioms GroupApproximation.AryLeavitt.balanced_component_isUnit
