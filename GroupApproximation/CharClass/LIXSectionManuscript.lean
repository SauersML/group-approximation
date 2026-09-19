import GroupApproximation.CharClass.LemmaTwoZero
import GroupApproximation.AlgTop.CPTautologicalSection

/-!
# The manuscript's data over `S⁵ × ∏ⱼ ℂP^{dⱼ}`, and its single zero

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LemmaTwoZero.lean` locates the zero of the transported section for *abstract*
block data `a, b, c`.  This file supplies the concrete data of the manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`, proof of
Lemma 2) over

```text
M = S⁵ × Y ,   Y = ∏ⱼ ℂP^{dⱼ} ,   V = 𝟏³ ⊕ H ,   H = ⊕ⱼ Lⱼ^{⊕dⱼ},
```

and discharges every hypothesis of `isMTSectionData_blockSplit` and of
`mtSection_manuscript_eq_zero_iff` except the one Step A owes, namely `G *ᵥ e = s`.

## The column, not the row

`H` is built from the rank-one projections themselves (`Hmat`), matching
`Analysis/LIXBlockProjections.lean`'s `lineProj`.  Its section must therefore be fixed by
those projections, and that forces the **column**
`AlgTop/CPTautologicalSection.lean`'s `tautColSection` and not the row `dualTautSection`:
the row is fixed by the *conjugate* projection, so with the row the `south_mem` field of
`IsMTSectionData` is not merely unproved but false.  The two have the same zero locus
(`tautColSection_eq_zero_iff`), so nothing downstream changes.

## Main results

* `Hmat`, `Vmat` — the projections, with `isStarProjection_Vmat` and `continuous_Vmat`.
* `Hmat_mulVec_cVec` — the transverse section is a section of `H`.
* `isMTSectionData_manuscriptData` — the manuscript's pair is section data for `W_g`,
  given Step A's `G *ᵥ e = s`.
* `manuscriptSection_eq_zero_iff_concrete` — **exactly one zero**: the section of `W_g`
  vanishes at `p` iff `p` is the south pole of the circle paired with
  `(-e₃, (basePoint)ⱼ)`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

/-! ## 1. `mulVec` through a block-diagonal matrix -/

/-- A block-diagonal matrix acts on a vector blockwise.  Mathlib has
`Matrix.blockDiagonal'_mul` but no `mulVec` companion at the pin. -/
theorem blockDiagonal'_mulVec {o : Type*} [Fintype o] [DecidableEq o] {m' : o → Type*}
    [∀ i, Fintype (m' i)] (M : ∀ i, Matrix (m' i) (m' i) ℂ) (v : (Σ i, m' i) → ℂ)
    (i : o) (k : m' i) :
    (Matrix.blockDiagonal' M *ᵥ v) ⟨i, k⟩ = (M i *ᵥ fun j => v ⟨i, j⟩) k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma (fun x : Σ i, m' i => Matrix.blockDiagonal' M ⟨i, k⟩ x * v x)]
  rw [Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun j _ => by rw [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## 2. The concrete base, index types and projections -/

variable {ℓ : ℕ}

/-- The blocks of `H = ⊕ⱼ Lⱼ^{⊕dⱼ}`: one for each `j` and each of the `dⱼ` copies. -/
abbrev HBlk (dd : Fin ℓ → ℕ) : Type := Σ j : Fin ℓ, Fin (dd j)

/-- The index type of `H`: inside the block `(j, i)` the fibre is `ℂ^{dⱼ+1}`. -/
abbrev HIdx (dd : Fin ℓ → ℕ) : Type := Σ b : HBlk dd, Fin (dd b.1 + 1)

/-- The index type of `V = 𝟏³ ⊕ H`. -/
abbrev VIdx (dd : Fin ℓ → ℕ) : Type := Fin 3 ⊕ HIdx dd

/-- `Y = ∏ⱼ ℂP^{dⱼ}`. -/
abbrev baseY (dd : Fin ℓ → ℕ) : Type := ∀ j : Fin ℓ, CP (dd j)

/-- `M = S⁵ × Y`, with `S⁵` the Hermitian unit sphere of `ℂ³`. -/
abbrev baseM (dd : Fin ℓ → ℕ) : Type := ↥(unitVectors (Fin 3)) × baseY dd

variable {dd : Fin ℓ → ℕ}

/-- `H = ⊕ⱼ Lⱼ^{⊕dⱼ}` in the projection model: block-diagonal, the block at `(j, i)` being
the rank-one projection which is the `j`-th coordinate of the point of `Y`. -/
def Hmat (m : baseM dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b : HBlk dd =>
    ((m.2 b.1 : CP (dd b.1)) : Matrix (Fin (dd b.1 + 1)) (Fin (dd b.1 + 1)) ℂ)

/-- `V = 𝟏³ ⊕ H`. -/
def Vmat (m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  Matrix.fromBlocks 1 0 0 (Hmat m)

theorem isStarProjection_Hmat (m : baseM dd) : IsStarProjection (Hmat m) := by
  constructor
  · show Hmat m * Hmat m = Hmat m
    rw [Hmat, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext fun b =>
      (isStarProjection_coe (m.2 b.1)).isIdempotentElem.eq)
  · show star (Hmat m) = Hmat m
    rw [Matrix.star_eq_conjTranspose, Hmat, Matrix.blockDiagonal'_conjTranspose]
    exact congrArg Matrix.blockDiagonal' (funext fun b =>
      conjTranspose_eq_of_isStarProjection (isStarProjection_coe (m.2 b.1)))

theorem isStarProjection_Vmat (m : baseM dd) : IsStarProjection (Vmat m) := by
  have hH := isStarProjection_Hmat m
  constructor
  · show Vmat m * Vmat m = Vmat m
    rw [Vmat, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simpa using hH.isIdempotentElem.eq
  · show star (Vmat m) = Vmat m
    rw [Matrix.star_eq_conjTranspose, Vmat, Matrix.fromBlocks_conjTranspose]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact Matrix.conjTranspose_one
    · exact Matrix.conjTranspose_zero
    · exact Matrix.conjTranspose_zero
    · have : star (Hmat m) = Hmat m := hH.isSelfAdjoint.star_eq
      rwa [Matrix.star_eq_conjTranspose] at this

/-- A continuous family of block-diagonal matrices.  Stated so that the dependent `cast`
inside `Matrix.blockDiagonal'_apply` never has to be handled: after `subst` on the block
index the `dite` is the `blockDiagonal'_apply_eq` branch. -/
theorem continuous_blockDiagonal' {X : Type*} [TopologicalSpace X] {o : Type*} [Fintype o]
    [DecidableEq o] {m' : o → Type*} [∀ i, Fintype (m' i)]
    {M : X → ∀ i, Matrix (m' i) (m' i) ℂ} (hM : ∀ i, Continuous fun x => M x i) :
    Continuous fun x => Matrix.blockDiagonal' (M x) := by
  refine continuous_matrix fun p q => ?_
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  by_cases h : i = j
  · subst h
    simpa using (hM i).matrix_elem a b
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact continuous_const

theorem continuous_Hmat : Continuous (Hmat (dd := dd)) :=
  continuous_blockDiagonal' fun b =>
    (continuous_coe (d := dd b.1)).comp ((continuous_apply b.1).comp continuous_snd)

theorem continuous_Vmat : Continuous (Vmat (dd := dd)) := by
  refine continuous_matrix fun p q => ?_
  cases p with
  | inl i =>
    cases q with
    | inl j => simpa [Vmat] using continuous_const
    | inr j => simpa [Vmat] using continuous_const
  | inr i =>
    cases q with
    | inl j => simpa [Vmat] using continuous_const
    | inr j => simpa [Vmat] using continuous_Hmat.matrix_elem i j

/-! ## 3. The three fields of the manuscript -/

/-- `e₃`, the manuscript's unit section `e` of the trivial block. -/
def eThree : Fin 3 → ℂ := Pi.single 2 1

/-- The manuscript's `e = (e₃, 0)`, constant in the base point. -/
def aVec (_m : baseM dd) : Fin 3 → ℂ := eThree

/-- The manuscript's `s = (x, 0)`, the tautological point of `S⁵`. -/
def bVec (m : baseM dd) : Fin 3 → ℂ := (m.1 : Fin 3 → ℂ)

/-- The manuscript's transverse section `σ` of `H`: on the block `(j, i)` it is the
`(i+1)`-st **column** of the `j`-th projection.  The column, not the row: see the header. -/
def cVec (m : baseM dd) : HIdx dd → ℂ :=
  fun p => entry (m.2 p.1.1) p.2 p.1.2.succ

@[simp]
theorem cVec_apply (m : baseM dd) (p : HIdx dd) :
    cVec m p = entry (m.2 p.1.1) p.2 p.1.2.succ := rfl

theorem eThree_normSq : ∑ i, ‖eThree i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_three]
  simp [eThree]

theorem eThree_ne_zero : eThree ≠ 0 := by
  intro h
  have h2 : eThree 2 = 0 := by rw [h]; rfl
  rw [eThree, Pi.single_eq_same] at h2
  exact one_ne_zero h2

theorem aVec_normSq (m : baseM dd) : ∑ i, ‖aVec m i‖ ^ 2 = 1 := eThree_normSq

theorem aVec_ne_zero (m : baseM dd) : aVec m ≠ 0 := eThree_ne_zero

theorem bVec_normSq (m : baseM dd) : ∑ i, ‖bVec m i‖ ^ 2 = 1 :=
  mem_unitVectors_iff.mp m.1.2

theorem continuous_aVec : Continuous (aVec (dd := dd)) := continuous_const

theorem continuous_bVec : Continuous (bVec (dd := dd)) :=
  continuous_subtype_val.comp continuous_fst

theorem continuous_cVec : Continuous (cVec (dd := dd)) := by
  refine continuous_pi fun p => ?_
  exact (continuous_entry _ _).comp ((continuous_apply p.1.1).comp continuous_snd)

/-! ## 4. The three fields take values in the range of `V` -/

/-- **The transverse section is a section of `H`.**  This is the identity the column
provides and the row does not: on each block the sum is an entry of `q * q = q`. -/
theorem Hmat_mulVec_cVec (m : baseM dd) : Hmat m *ᵥ cVec m = cVec m := by
  funext p
  obtain ⟨b, k⟩ := p
  rw [Hmat, blockDiagonal'_mulVec]
  show (∑ k', entry (m.2 b.1) k k' * entry (m.2 b.1) k' b.2.succ) = entry (m.2 b.1) k b.2.succ
  exact entry_sum_mul (m.2 b.1) k b.2.succ

theorem Vmat_mulVec_left (m : baseM dd) (u : Fin 3 → ℂ) :
    Vmat m *ᵥ Sum.elim u (0 : HIdx dd → ℂ) = Sum.elim u (0 : HIdx dd → ℂ) := by
  rw [Vmat, Matrix.fromBlocks_mulVec]
  congr 1 <;> simp

theorem Vmat_mulVec_right (m : baseM dd) :
    Vmat m *ᵥ Sum.elim (0 : Fin 3 → ℂ) (cVec m) = Sum.elim (0 : Fin 3 → ℂ) (cVec m) := by
  rw [Vmat, Matrix.fromBlocks_mulVec]
  congr 1
  · simp
  · simpa using Hmat_mulVec_cVec m

/-! ## 5. The section data, and the single zero -/

variable {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}

/-- **The manuscript's pair is section data for `W_g`.**  Every hypothesis is discharged
here except `hGa`, which is Step A's `g e = s`. -/
theorem isMTSectionData_manuscriptData {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}
    {χ : ℝ → ℝ} (hch : IsCircleChart y t) (hχ : Continuous χ) (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (hGa : ∀ m : baseM dd, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    IsMTSectionData Vmat G y t (blockNorth aVec)
      (blockSouth (Z := Z) aVec bVec cVec χ y) :=
  isMTSectionData_blockSplit hch continuous_aVec continuous_bVec continuous_cVec hχ hχ0 hχ1
    (fun m => Vmat_mulVec_left m (aVec m)) (fun m => Vmat_mulVec_left m (bVec m))
    Vmat_mulVec_right hGa

/-- The point of `S⁵` antipodal to `e₃`. -/
def negEThree : ↥(unitVectors (Fin 3)) :=
  ⟨fun i => -eThree i, by
    rw [mem_unitVectors_iff]
    simpa using eThree_normSq⟩

/-- The base point of `Y`. -/
def baseYPoint (dd : Fin ℓ → ℕ) : baseY dd := fun j => basePoint (dd j)

/-- The transverse section vanishes exactly at the base point of `Y`. -/
theorem cVec_eq_zero_iff (m : baseM dd) : cVec m = 0 ↔ m.2 = baseYPoint dd := by
  constructor
  · intro h
    funext j
    refine (tautColSection_eq_zero_iff (m.2 j)).mp fun i k => ?_
    have := congrFun h (⟨⟨j, i⟩, k⟩ : HIdx dd)
    simpa using this
  · intro h
    funext p
    have hj : m.2 p.1.1 = basePoint (dd p.1.1) := by rw [h]; rfl
    have := (tautColSection_eq_zero_iff (m.2 p.1.1)).mpr hj p.1.2 p.2
    simpa using this

/-- The trivial-block condition of the zero locus says the sphere coordinate is antipodal
to `e₃`. -/
theorem bVec_eq_neg_aVec_iff (m : baseM dd) : bVec m = -aVec m ↔ m.1 = negEThree := by
  constructor
  · intro h
    refine Subtype.ext (funext fun i => ?_)
    have := congrFun h i
    simpa [bVec, aVec, negEThree] using this
  · intro h
    funext i
    have : (m.1 : Fin 3 → ℂ) i = -eThree i := by rw [h]; rfl
    simpa [bVec, aVec] using this

/-- **Exactly one zero.**  Over `S¹ × S⁵ × Y` the manuscript's section of the mapping
torus vanishes at `p` if and only if `p` is the south pole of the circle paired with the
single base point `(-e₃, (basePoint)ⱼ)`.  No characteristic class, no orientation, no
counting measure. -/
theorem manuscriptSection_eq_zero_iff_concrete
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} {χ : ℝ → ℝ} (hch : IsCircleChart y t)
    (hd : IsMTSectionData Vmat G y t (blockNorth aVec) (blockSouth (Z := Z) aVec bVec cVec χ y))
    (hχhalf : χ (1 / 2 : ℝ) = 1) (p : Z × baseM dd) :
    mtSection Vmat G y t (blockNorth aVec) (blockSouth aVec bVec cVec χ y) p = 0
      ↔ (t p.1 = -1 ∧ y p.1 = 0 ∧ p.2.1 = negEThree ∧ p.2.2 = baseYPoint dd) := by
  rw [mtSection_manuscript_eq_zero_iff hch hd aVec_ne_zero aVec_normSq bVec_normSq hχhalf p]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (bVec_eq_neg_aVec_iff p.2).mp h3, (cVec_eq_zero_iff p.2).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (bVec_eq_neg_aVec_iff p.2).mpr h3, (cVec_eq_zero_iff p.2).mpr h4⟩

end GroupApproximation.CharClass
