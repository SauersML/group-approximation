import GroupApproximation.CharClass.LIXShapeGenericRank
import GroupApproximation.CharClass.LIXKGenPunctured
import GroupApproximation.CharClass.SliceVLineRoots
import GroupApproximation.CharClass.SliceReindex

/-!
# `V = 𝟏^{n+1} ⊕ H` as a sum of lines, at sphere rank `n`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm.

The splitting principle consumes a bundle presented as a pointwise sum of rank-one
projections indexed by `Finset.range r`.  `LIXVDecomposition`, `LIXVBundle`, `LIXVLineBundles`,
`SliceVFlat`, `SliceVLinesY` and `SliceVLineRoots` do this for `V = 𝟏³ ⊕ H`.  This file is the
same material with the trivial summand `𝟏^{n+1}`, over `sp-tower`'s rank-`n` shape layer
(`CharClass/LIXShapeGeneric.lean`).

No coefficients appear: everything here is matrices and bundles, so the `F₂` slice value
(`lx-slice2`) and the slice value over a field (`lx-sliceK`) import the one copy.

The lines are written over the point of `Y` alone, because `V` does not see the sphere
coordinate; `vLine` over `M = S^{2n+1} × Y` is `vLineY` read at `m.2`.  The rank is
`KGen.lixRank n dd`, the one `KGen.rank_lixBundle` uses.

## The multiplicity

`HBlk dd` is `Σ j, Fin (dd j)`, so the tautological line of the `j`-th projective factor appears
`dd j` times, not once.  `n + 1` constant lines and `∑ⱼ dⱼ` tautological ones make
`KGen.lixRank n dd = (∑ⱼ dⱼ) + (n + 1)`.

## Main declarations

* `Gen.trivLine`, `Gen.hLine`, `Gen.vLineY`, `Gen.vLine` — the lines.
* `Gen.VmatY_eq_sum_lines`, `Gen.Vmat_eq_sum_lines` — **the pointwise sum**.
* `Gen.vBundleY`, `Gen.rank_vBundleY` — `V` as a bundle over `Y`, with its rank.
* `Gen.vLineYBundle` — the lines as bundles.
* `Gen.vIndexEquiv`, `Gen.vLineFlatBundle`, `Gen.sum_vLineFlatBundle` — flattened to a range.
* `Gen.blockEmb`, `Gen.vLineYBundle_inr_eq` — a block line is the tautological line of its
  factor, pushed into the block.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn
open GroupApproximation.CharClass.Bundle

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The lines -/

/-- The `i`-th constant line of the trivial summand `𝟏^{n+1}`. -/
def trivLine (n : ℕ) (i : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun a c => if a = i ∧ c = i then 1 else 0

/-- The tautological line sitting in the block `b`, over the point of `Y` alone. -/
def hLine (b : HBlk dd) (y : baseY dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b' : HBlk dd =>
    if b' = b then ((y b'.1 : CP (dd b'.1)) :
      Matrix (Fin (dd b'.1 + 1)) (Fin (dd b'.1 + 1)) ℂ) else 0

/-- **The lines of `V` at rank `n`**, over the point of `Y`, indexed by `Fin (n+1) ⊕ HBlk dd`. -/
def vLineY (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (y : baseY dd) :
    Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  match b with
  | Sum.inl i => Matrix.fromBlocks (trivLine n i) 0 0 0
  | Sum.inr b => Matrix.fromBlocks 0 0 0 (hLine b y)

/-- The lines over `M = S^{2n+1} × Y`, which do not see the sphere coordinate. -/
def vLine (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (m : baseM n dd) :
    Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  vLineY n b m.2

/-- `V` over the point of `Y` alone.  `VmatY_eq` records that it is `Gen.Vmat n` on the nose. -/
def VmatY (n : ℕ) (y : baseY dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Matrix.fromBlocks 1 0 0 (Hmat y)

theorem VmatY_eq (n : ℕ) (m : baseM n dd) : VmatY n m.2 = Vmat n m := rfl

/-! ## 2. Each line has trace one -/

theorem trace_trivLine (n : ℕ) (i : Fin (n + 1)) : Matrix.trace (trivLine n i) = 1 := by
  rw [Matrix.trace]
  simp [Matrix.diag, trivLine]

theorem trace_hLine (b : HBlk dd) (y : baseY dd) : Matrix.trace (hLine b y) = 1 := by
  rw [hLine, Matrix.trace_blockDiagonal']
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    exact AlgTop.CPn.trace_coe (y b.1)
  · intro b' _ hne
    rw [if_neg hne, Matrix.trace_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem trace_vLineY (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (y : baseY dd) :
    Matrix.trace (vLineY n b y) = 1 := by
  cases b with
  | inl i => rw [vLineY, trace_fromBlocks_gen, trace_trivLine, Matrix.trace_zero, add_zero]
  | inr b => rw [vLineY, trace_fromBlocks_gen, Matrix.trace_zero, trace_hLine, zero_add]

theorem trace_vLine (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (m : baseM n dd) :
    Matrix.trace (vLine n b m) = 1 :=
  trace_vLineY n b m.2

/-! ## 3. The pointwise sum -/

theorem sum_trivLine (n : ℕ) :
    (∑ i : Fin (n + 1), trivLine n i) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  ext a c
  rw [Matrix.sum_apply]
  simp only [trivLine, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro i _ hne
      exact if_neg fun hh => hne hh.1.symm
    · intro hc
      exact absurd (Finset.mem_univ a) hc
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact if_neg fun hh => h (hh.1.trans hh.2.symm)

theorem sum_hLine (y : baseY dd) : (∑ b : HBlk dd, hLine b y) = Hmat y := by
  ext p q
  obtain ⟨b₁, i⟩ := p
  obtain ⟨b₂, jj⟩ := q
  rw [Matrix.sum_apply]
  by_cases h : b₁ = b₂
  · subst h
    rw [Hmat, Matrix.blockDiagonal'_apply_eq]
    rw [Finset.sum_eq_single b₁]
    · rw [hLine, Matrix.blockDiagonal'_apply_eq, if_pos rfl]
    · intro b' _ hne
      rw [hLine, Matrix.blockDiagonal'_apply_eq, if_neg (Ne.symm hne)]
      rfl
    · intro hc
      exact absurd (Finset.mem_univ b₁) hc
  · rw [Hmat, Matrix.blockDiagonal'_apply_ne _ _ _ h]
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [hLine, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- **`V` is the pointwise sum of its lines**, over the point of `Y`. -/
theorem VmatY_eq_sum_lines (n : ℕ) (y : baseY dd) :
    VmatY n y = ∑ b : Fin (n + 1) ⊕ HBlk dd, vLineY n b y := by
  rw [Fintype.sum_sum_type]
  ext p q
  rw [Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply, VmatY]
  cases p with
  | inl a =>
      cases q with
      | inl c =>
          rw [Matrix.fromBlocks_apply₁₁]
          have hz : ∀ b : HBlk dd, vLineY n (Sum.inr b) y (Sum.inl a) (Sum.inl c) = 0 :=
            fun _ => rfl
          rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hz b,
            Finset.sum_const_zero, add_zero]
          have hv : ∀ i : Fin (n + 1),
              vLineY n (Sum.inl i) y (Sum.inl a) (Sum.inl c) = trivLine n i a c := fun _ => rfl
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hv i]
          rw [← Matrix.sum_apply, sum_trivLine]
      | inr c =>
          simp [vLineY]
  | inr a =>
      cases q with
      | inl c =>
          simp [vLineY]
      | inr c =>
          rw [Matrix.fromBlocks_apply₂₂]
          have hz : ∀ i : Fin (n + 1), vLineY n (Sum.inl i) y (Sum.inr a) (Sum.inr c) = 0 :=
            fun _ => rfl
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hz i,
            Finset.sum_const_zero, zero_add]
          have hv : ∀ b : HBlk dd,
              vLineY n (Sum.inr b) y (Sum.inr a) (Sum.inr c) = hLine b y a c := fun _ => rfl
          rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hv b]
          rw [← Matrix.sum_apply, sum_hLine]

/-- **`V` is the pointwise sum of its lines**, over `M = S^{2n+1} × Y`. -/
theorem Vmat_eq_sum_lines (n : ℕ) (m : baseM n dd) :
    Vmat n m = ∑ b : Fin (n + 1) ⊕ HBlk dd, vLine n b m :=
  VmatY_eq_sum_lines n m.2

/-! ## 4. `V` as a bundle over `Y`, with its rank -/

theorem continuous_VmatY (n : ℕ) : Continuous (VmatY (dd := dd) n) := by
  have h : Continuous fun y : baseY dd => Vmat n ((negELast n, y) : baseM n dd) :=
    (continuous_Vmat n).comp (continuous_const.prodMk continuous_id)
  exact h

theorem isStarProjection_VmatY (n : ℕ) (y : baseY dd) : IsStarProjection (VmatY n y) :=
  isStarProjection_Vmat n ((negELast n, y) : baseM n dd)

/-- **`V = 𝟏^{n+1} ⊕ H` as a bundle over the projective base.** -/
def vBundleY (n : ℕ) (dd : Fin ℓ → ℕ) : Bundle (baseY dd) (VIdx n dd) where
  toFun := VmatY n
  continuous_toFun := continuous_VmatY n
  isStarProjection_toFun := isStarProjection_VmatY n

@[simp] theorem coe_vBundleY (n : ℕ) : ⇑(vBundleY n dd) = VmatY (dd := dd) n := rfl

theorem trace_VmatY (n : ℕ) (y : baseY dd) :
    Matrix.trace (VmatY n y) = (((∑ j, dd j : ℕ) + (n + 1) : ℕ) : ℂ) :=
  trace_Vmat n ((negELast n, y) : baseM n dd)

/-- **The rank of `V`**, in the `Bundle.rank` form the splitting principle consumes. -/
theorem rank_vBundleY (n : ℕ) (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY n dd).rank y = KGen.lixRank n dd := by
  have htr : Matrix.trace ((vBundleY n dd) y) = ((KGen.lixRank n dd : ℕ) : ℂ) := by
    show Matrix.trace (VmatY n y) = _
    exact trace_VmatY n y
  have h := Bundle.trace_eq_rank (vBundleY n dd) y
  rw [htr] at h
  exact_mod_cast h.symm

theorem kgenLixRank_pos (n : ℕ) (dd : Fin ℓ → ℕ) : 0 < KGen.lixRank n dd := by
  rw [KGen.lixRank]
  omega

/-! ## 5. The lines as bundles -/

theorem isStarProjection_trivLine (n : ℕ) (i : Fin (n + 1)) :
    IsStarProjection (trivLine n i) := by
  constructor
  · show trivLine n i * trivLine n i = trivLine n i
    ext a c
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases h : a = i <;> by_cases h' : c = i <;> simp [trivLine, h, h']
    · intro d _ hne
      by_cases h : a = i <;> simp [trivLine, h, hne]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  · show star (trivLine n i) = trivLine n i
    rw [Matrix.star_eq_conjTranspose]
    ext a c
    simp only [Matrix.conjTranspose_apply, trivLine]
    by_cases h : c = i <;> by_cases h' : a = i <;> simp [h, h']

theorem isStarProjection_hLine (b : HBlk dd) (y : baseY dd) :
    IsStarProjection (hLine b y) := by
  constructor
  · show hLine b y * hLine b y = hLine b y
    rw [hLine, ← Matrix.blockDiagonal'_mul]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact (isStarProjection_coe (y b'.1)).isIdempotentElem.eq
    · rw [if_neg h, Matrix.mul_zero]
  · show star (hLine b y) = hLine b y
    rw [Matrix.star_eq_conjTranspose, hLine, Matrix.blockDiagonal'_conjTranspose]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact conjTranspose_eq_of_isStarProjection (isStarProjection_coe (y b'.1))
    · rw [if_neg h, Matrix.conjTranspose_zero]

theorem continuous_hLine (b : HBlk dd) : Continuous fun y : baseY dd => hLine b y := by
  show Continuous fun y : baseY dd => Matrix.blockDiagonal' fun b' : HBlk dd =>
    if b' = b then ((y b'.1 : CP (dd b'.1)) :
      Matrix (Fin (dd b'.1 + 1)) (Fin (dd b'.1 + 1)) ℂ) else 0
  refine continuous_blockDiagonal' fun b' => ?_
  by_cases h : b' = b
  · simp only [if_pos h]
    exact (continuous_coe (d := dd b'.1)).comp (continuous_apply b'.1)
  · simp only [if_neg h]
    exact continuous_const

/-- **Each line is a star projection.** -/
theorem isStarProjection_vLineY (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (y : baseY dd) :
    IsStarProjection (vLineY n b y) := by
  cases b with
  | inl i =>
      have hP := isStarProjection_trivLine n i
      constructor
      · show Matrix.fromBlocks (trivLine n i) 0 0 (0 : Matrix (HIdx dd) (HIdx dd) ℂ) *
            Matrix.fromBlocks (trivLine n i) 0 0 0 = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simpa using hP.isIdempotentElem.eq
        · simp
        · simp
        · simp
      · show star (Matrix.fromBlocks (trivLine n i) 0 0
          (0 : Matrix (HIdx dd) (HIdx dd) ℂ)) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · have : star (trivLine n i) = trivLine n i := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
  | inr b =>
      have hP := isStarProjection_hLine b y
      constructor
      · show Matrix.fromBlocks (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 (hLine b y) *
            Matrix.fromBlocks 0 0 0 (hLine b y) = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp
        · simpa using hP.isIdempotentElem.eq
      · show star (Matrix.fromBlocks (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0
          (hLine b y)) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · have : star (hLine b y) = hLine b y := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this

/-- **Each line is continuous.** -/
theorem continuous_vLineY (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) :
    Continuous (vLineY (dd := dd) n b) := by
  cases b with
  | inl i => exact continuous_const
  | inr b =>
      refine continuous_matrix fun p q => ?_
      cases p with
      | inl a => cases q <;> exact continuous_const
      | inr a =>
          cases q with
          | inl c => exact continuous_const
          | inr c => exact (continuous_hLine b).matrix_elem a c

/-- **The lines of `V`, as bundles**, over the same base as `vBundleY`. -/
def vLineYBundle (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) : Bundle (baseY dd) (VIdx n dd) where
  toFun := vLineY n b
  continuous_toFun := continuous_vLineY n b
  isStarProjection_toFun := isStarProjection_vLineY n b

@[simp] theorem coe_vLineYBundle (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) :
    ⇑(vLineYBundle n b) = vLineY (dd := dd) n b := rfl

theorem trace_vLineYBundle (n : ℕ) (b : Fin (n + 1) ⊕ HBlk dd) (y : baseY dd) :
    ((vLineYBundle n b) y).trace = 1 :=
  trace_vLineY n b y

/-! ## 6. Flattening to a range -/

theorem card_vIndex (n : ℕ) (dd : Fin ℓ → ℕ) :
    Fintype.card (Fin (n + 1) ⊕ HBlk dd) = KGen.lixRank n dd := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, KGen.lixRank]
  simp only [Fintype.card_fin]
  omega

/-- The equivalence of the block index with a flat range of the rank's size. -/
def vIndexEquiv (n : ℕ) (dd : Fin ℓ → ℕ) : (Fin (n + 1) ⊕ HBlk dd) ≃ Fin (KGen.lixRank n dd) :=
  Fintype.equivFinOfCardEq (card_vIndex n dd)

/-- The lines over the projective base, indexed by a natural and zero off the range. -/
def vLineYFlat (n : ℕ) (dd : Fin ℓ → ℕ) (y : baseY dd) (l : ℕ) :
    Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  if h : l < KGen.lixRank n dd then vLineY n ((vIndexEquiv n dd).symm ⟨l, h⟩) y else 0

theorem vLineYFlat_apply_equiv (n : ℕ) (dd : Fin ℓ → ℕ) (y : baseY dd)
    (b : Fin (n + 1) ⊕ HBlk dd) :
    vLineYFlat n dd y ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) = vLineY n b y := by
  have hlt : ((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ) < KGen.lixRank n dd :=
    (vIndexEquiv n dd b).isLt
  have hb : (vIndexEquiv n dd).symm
      ⟨((vIndexEquiv n dd b : Fin (KGen.lixRank n dd)) : ℕ), hlt⟩ = b := by
    rw [Fin.eta]
    exact (vIndexEquiv n dd).symm_apply_apply b
  rw [vLineYFlat, dif_pos hlt, hb]

/-- **The decomposition over the projective base, over a flat range.** -/
theorem VmatY_eq_sum_rangeY (n : ℕ) (y : baseY dd) :
    VmatY n y = ∑ l ∈ Finset.range (KGen.lixRank n dd), vLineYFlat n dd y l := by
  rw [sum_range_of_equiv (KGen.lixRank n dd) (vIndexEquiv n dd) (fun b => vLineY n b y)
    (vLineYFlat n dd y) (vLineYFlat_apply_equiv n dd y)]
  exact VmatY_eq_sum_lines n y

/-- The lines as bundles, indexed by a natural, reading the index modulo the rank: every member
is a genuine line, so its trace is one at every index. -/
def vLineFlatBundle (n : ℕ) (dd : Fin ℓ → ℕ) (l : ℕ) : Bundle (baseY dd) (VIdx n dd) :=
  vLineYBundle n ((vIndexEquiv n dd).symm
    ⟨l % KGen.lixRank n dd, Nat.mod_lt _ (kgenLixRank_pos n dd)⟩)

theorem trace_vLineFlatBundle (n : ℕ) (dd : Fin ℓ → ℕ) (l : ℕ) (y : baseY dd) :
    Matrix.trace ((vLineFlatBundle n dd l) y) = 1 :=
  trace_vLineY n _ y

theorem trace_vLineFlatBundle_lt (n : ℕ) (dd : Fin ℓ → ℕ) (l : ℕ) (_hl : l < KGen.lixRank n dd)
    (y : baseY dd) : Matrix.trace ((vLineFlatBundle n dd l) y) = 1 :=
  trace_vLineFlatBundle n dd l y

theorem vLineFlatBundle_apply_lt (n : ℕ) (dd : Fin ℓ → ℕ) (l : ℕ) (hl : l < KGen.lixRank n dd)
    (y : baseY dd) : (vLineFlatBundle n dd l) y = vLineYFlat n dd y l := by
  have h : (⟨l % KGen.lixRank n dd, Nat.mod_lt _ (kgenLixRank_pos n dd)⟩ :
      Fin (KGen.lixRank n dd)) = ⟨l, hl⟩ := Fin.ext (Nat.mod_eq_of_lt hl)
  show vLineY n ((vIndexEquiv n dd).symm ⟨l % KGen.lixRank n dd, _⟩) y = _
  rw [h, vLineYFlat, dif_pos hl]

/-- **The decomposition of `V` into the flat family**, in the form the split relation takes. -/
theorem sum_vLineFlatBundle (n : ℕ) (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY n dd) y = ∑ l ∈ Finset.range (KGen.lixRank n dd), (vLineFlatBundle n dd l) y := by
  show VmatY n y = _
  rw [VmatY_eq_sum_rangeY n y]
  exact Finset.sum_congr rfl fun l hl =>
    (vLineFlatBundle_apply_lt n dd l (Finset.mem_range.mp hl) y).symm

/-! ## 7. A block line is the tautological line of its factor -/

/-- The index of the block `β` sits inside the index of `V`. -/
def blockEmb (n : ℕ) (β : HBlk dd) : Fin (dd β.1 + 1) → VIdx n dd := fun i => Sum.inr ⟨β, i⟩

theorem blockEmb_injective (n : ℕ) (β : HBlk dd) : Function.Injective (blockEmb n β) := by
  intro i j h
  have h1 : (⟨β, i⟩ : HIdx dd) = ⟨β, j⟩ := Sum.inr.inj h
  rw [Sigma.mk.injEq] at h1
  exact eq_of_heq h1.2

/-- On its own block, `hLine` is the tautological projection. -/
theorem hLine_apply_eq (β : HBlk dd) (y : baseY dd) (i j : Fin (dd β.1 + 1)) :
    hLine β y ⟨β, i⟩ ⟨β, j⟩
      = ((y β.1 : CP (dd β.1)) : Matrix (Fin (dd β.1 + 1)) (Fin (dd β.1 + 1)) ℂ) i j := by
  simp only [hLine]
  rw [Matrix.blockDiagonal'_apply_eq, if_pos rfl]

/-- Off its own block in the row, `hLine` vanishes. -/
theorem hLine_apply_ne_fst (β : HBlk dd) (y : baseY dd) {b₁ b₂ : HBlk dd}
    (i : Fin (dd b₁.1 + 1)) (j : Fin (dd b₂.1 + 1)) (h : b₁ ≠ β) :
    hLine β y ⟨b₁, i⟩ ⟨b₂, j⟩ = 0 := by
  by_cases hb : b₁ = b₂
  · subst hb
    simp only [hLine]
    rw [Matrix.blockDiagonal'_apply_eq, if_neg h]
    rfl
  · exact Matrix.blockDiagonal'_apply_ne
      (m' := fun b : HBlk dd => Fin (dd b.1 + 1))
      (n' := fun b : HBlk dd => Fin (dd b.1 + 1)) _ i j hb

/-- Off its own block in the column, `hLine` vanishes. -/
theorem hLine_apply_ne_snd (β : HBlk dd) (y : baseY dd) {b₂ : HBlk dd}
    (i : Fin (dd β.1 + 1)) (j : Fin (dd b₂.1 + 1)) (h : b₂ ≠ β) :
    hLine β y ⟨β, i⟩ ⟨b₂, j⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne
      (m' := fun b : HBlk dd => Fin (dd b.1 + 1))
      (n' := fun b : HBlk dd => Fin (dd b.1 + 1)) _ i j (Ne.symm h)

/-- **The line in block `β` is the tautological line of its factor, pushed into the block.** -/
theorem vLineY_inr_eq (n : ℕ) (β : HBlk dd) (y : baseY dd) :
    vLineY n (Sum.inr β) y
      = coordIncl (blockEmb n β) * (LH.cpTautY dd β.1) y * (coordIncl (blockEmb n β))ᴴ := by
  have hrow : ∀ (b : HBlk dd) (i : Fin (dd b.1 + 1)), ¬ (b = β) →
      ∀ k, (Sum.inr ⟨b, i⟩ : VIdx n dd) ≠ blockEmb n β k :=
    fun b i hb k h => hb (congrArg Sigma.fst (Sum.inr.inj h))
  simp only [vLineY]
  ext p q
  rcases p with a | ⟨b₁, i⟩
  · rw [coordIncl_conj_apply_row (f := blockEmb n β) (fun _ => Sum.inl_ne_inr) _ q]
    rcases q with c | ⟨b₂, j⟩ <;> rfl
  · rcases q with c | ⟨b₂, j⟩
    · rw [coordIncl_conj_apply_col (f := blockEmb n β) (fun _ => Sum.inl_ne_inr) _
        (Sum.inr ⟨b₁, i⟩)]
      rfl
    · show hLine β y ⟨b₁, i⟩ ⟨b₂, j⟩ = _
      by_cases hb1 : b₁ = β
      · by_cases hb2 : b₂ = β
        · subst hb1
          subst hb2
          rw [hLine_apply_eq]
          exact (coordIncl_conj_apply (blockEmb_injective n _) _ i j).symm
        · subst hb1
          rw [hLine_apply_ne_snd _ _ i j hb2]
          exact (coordIncl_conj_apply_col (hrow b₂ j hb2) _ _).symm
      · rw [hLine_apply_ne_fst _ _ i j hb1]
        exact (coordIncl_conj_apply_row (hrow b₁ i hb1) _ _).symm

/-- The same, as bundles. -/
theorem vLineYBundle_inr_eq (n : ℕ) (β : HBlk dd) :
    vLineYBundle n (Sum.inr β)
      = pushforward (blockEmb n β) (blockEmb_injective n β) (LH.cpTautY dd β.1) :=
  DFunLike.ext _ _ (fun y => vLineY_inr_eq n β y)

end Gen

end GroupApproximation.CharClass
