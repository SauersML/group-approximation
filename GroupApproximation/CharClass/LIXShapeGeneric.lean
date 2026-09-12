import GroupApproximation.CharClass.LemmaTwoStatement
import GroupApproximation.Analysis.LIXGeneratorUnitary

/-!
# The manuscript's data over `S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`, generic in the rank

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

`CharClass/LIXSectionManuscript.lean` and `CharClass/LemmaTwoStatement.lean` fix the
manuscript's shape at rank two:

```text
M = S⁵ × Y ,  V = 𝟏³ ⊕ H ,  VIdx = Fin 3 ⊕ HIdx ,  e = e₃ .
```

This file re-authors that shape with the rank `n` as a parameter,

```text
M = S^{2n+1} × Y ,  V = 𝟏^{n+1} ⊕ H ,  VIdx n = Fin (n+1) ⊕ HIdx ,  e = e_last ,
```

and closes the loop by proving that every rank-two name of the two files above is
**definitionally** its `n = 2` instance (`§7`), so the existing closure is untouched and
`Gen` is available to anything that wants a general rank.

## What is and is not parametrised here

Only the **rank**.  The coefficient datum `dd : Fin ℓ → ℕ` — and with it `HBlk`, `HIdx`,
`baseY`, `basePoint` — is already generic in the rank-two files and is re-used verbatim;
generalising *it* is another lane's business.  The one adjustment made to the `dd` side
is bookkeeping, not mathematics: `Hmat` and `cVec` are re-indexed by the point of `Y`
alone rather than by the pair `(x, y) ∈ M`, because at general rank the first factor of
`M` changes while `H` does not.  `Hmat_eq` and `cVec_eq` record that this is a `rfl`.

## The constant section is the generator's pole

`eLast n` is `Pi.single (Fin.last n) 1`, which is *the same term* as
`LIX.Gen.ePole n` — the point of `S^{2n+1}` at which
`Analysis/LIXGeneratorUnitary.lean`'s `Gen.genU n` is trivialised.  `eLast_eq_ePole`
proves this by `rfl`.  That is the reason the constant section stays at the **last**
coordinate rather than moving to the first: the analysis side's Householder frames are
built around `Fin.last n`, and any other choice would put a permutation between the two
sides of Step A for no gain.

## Main results

* `Gen.VIdx`, `Gen.baseM`, `Gen.Vmat` — the ambient, at rank `n`.
* `Gen.eLast`, `Gen.aVec`, `Gen.bVec`, `Gen.cVec` — the three fields.
* `Gen.sProj`, `Gen.eProj`, `Gen.FHmat`, `Gen.EHmat` — the two complements in one ambient.
* `Gen.isMTSectionData_manuscriptData` — the manuscript's pair is section data for `W_g`.
* `Gen.manuscriptSection_eq_zero_iff_concrete` — **exactly one zero**, at every rank.
* `Gen.HasStepAUnitary` — Step A's output, at rank `n`.
* `§7` — the `n = 2` bridges, every one of them `rfl`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ}

/-! ## 1. The ambient at rank `n` -/

/-- The index type of `V = 𝟏^{n+1} ⊕ H`.  At `n = 2` this is `CharClass.VIdx`. -/
abbrev VIdx (n : ℕ) (dd : Fin ℓ → ℕ) : Type := Fin (n + 1) ⊕ HIdx dd

/-- `M = S^{2n+1} × Y`, with `S^{2n+1}` the Hermitian unit sphere of `ℂ^{n+1}`.  This is
`STW59.Gen.sphereOdd n` paired with the coefficient base; at `n = 2` it is
`CharClass.baseM`. -/
abbrev baseM (n : ℕ) (dd : Fin ℓ → ℕ) : Type :=
  ↥(unitVectors (Fin (n + 1))) × baseY dd

variable {dd : Fin ℓ → ℕ}

/-- `H = ⊕ⱼ Lⱼ^{⊕dⱼ}`, indexed by the point of `Y` alone.  The rank-two file indexes it
by the pair; `Hmat_eq` records that the two agree on the nose. -/
def Hmat (y : baseY dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b : HBlk dd =>
    ((y b.1 : CP (dd b.1)) : Matrix (Fin (dd b.1 + 1)) (Fin (dd b.1 + 1)) ℂ)

/-- `V = 𝟏^{n+1} ⊕ H`. -/
def Vmat (n : ℕ) (m : baseM n dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Matrix.fromBlocks 1 0 0 (Hmat m.2)

theorem isStarProjection_Hmat (y : baseY dd) : IsStarProjection (Hmat y) := by
  constructor
  · show Hmat y * Hmat y = Hmat y
    rw [Hmat, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext fun b =>
      (isStarProjection_coe (y b.1)).isIdempotentElem.eq)
  · show star (Hmat y) = Hmat y
    rw [Matrix.star_eq_conjTranspose, Hmat, Matrix.blockDiagonal'_conjTranspose]
    exact congrArg Matrix.blockDiagonal' (funext fun b =>
      conjTranspose_eq_of_isStarProjection (isStarProjection_coe (y b.1)))

theorem isStarProjection_Vmat (n : ℕ) (m : baseM n dd) : IsStarProjection (Vmat n m) := by
  have hH := isStarProjection_Hmat m.2
  constructor
  · show Vmat n m * Vmat n m = Vmat n m
    rw [Vmat, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simpa using hH.isIdempotentElem.eq
  · show star (Vmat n m) = Vmat n m
    rw [Matrix.star_eq_conjTranspose, Vmat, Matrix.fromBlocks_conjTranspose]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact Matrix.conjTranspose_one
    · exact Matrix.conjTranspose_zero
    · exact Matrix.conjTranspose_zero
    · have h : star (Hmat m.2) = Hmat m.2 := hH.isSelfAdjoint.star_eq
      rwa [Matrix.star_eq_conjTranspose] at h

theorem continuous_Hmat : Continuous (Hmat (dd := dd)) :=
  continuous_blockDiagonal' fun b =>
    (continuous_coe (d := dd b.1)).comp (continuous_apply b.1)

theorem continuous_Vmat (n : ℕ) : Continuous (Vmat (dd := dd) n) := by
  refine continuous_matrix fun p q => ?_
  have hH : Continuous fun m : baseM n dd => Hmat m.2 :=
    continuous_Hmat.comp' continuous_snd
  cases p with
  | inl i =>
    cases q with
    | inl j => simpa [Vmat] using continuous_const
    | inr j => simpa [Vmat] using continuous_const
  | inr i =>
    cases q with
    | inl j => simpa [Vmat] using continuous_const
    | inr j => simpa [Vmat] using hH.matrix_elem i j

/-! ## 2. The three fields at rank `n` -/

/-- `e_last`, the manuscript's unit section `e` of the trivial block.  This is
`LIX.Gen.ePole n`; see `eLast_eq_ePole`. -/
def eLast (n : ℕ) : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1

/-- The constant section of the shape layer is the pole of the analysis layer's
generator.  Both are `Pi.single (Fin.last n) 1`, so this is a `rfl`; it is stated so that
Step A never has to insert a permutation between the two sides. -/
theorem eLast_eq_ePole (n : ℕ) : eLast n = LIX.Gen.ePole n := rfl

/-- The manuscript's `e = (e_last, 0)`, constant in the base point. -/
def aVec (n : ℕ) (_m : baseM n dd) : Fin (n + 1) → ℂ := eLast n

/-- The manuscript's `s = (x, 0)`, the tautological point of `S^{2n+1}`. -/
def bVec (n : ℕ) (m : baseM n dd) : Fin (n + 1) → ℂ := (m.1 : Fin (n + 1) → ℂ)

/-- The manuscript's transverse section `σ` of `H`, indexed by the point of `Y` alone: on
the block `(j, i)` it is the `(i+1)`-st **column** of the `j`-th projection. -/
def cVec (y : baseY dd) : HIdx dd → ℂ :=
  fun p => entry (y p.1.1) p.2 p.1.2.succ

@[simp]
theorem cVec_apply (y : baseY dd) (p : HIdx dd) :
    cVec y p = entry (y p.1.1) p.2 p.1.2.succ := rfl

theorem eLast_normSq (n : ℕ) : ∑ i, ‖eLast n i‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [eLast, Pi.single_eq_same]
    simp
  · intro b _ hb
    rw [eLast, Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eLast_ne_zero (n : ℕ) : eLast n ≠ 0 := by
  intro h
  have h2 : eLast n (Fin.last n) = 0 := by rw [h]; rfl
  rw [eLast, Pi.single_eq_same] at h2
  exact one_ne_zero h2

theorem aVec_normSq (n : ℕ) (m : baseM n dd) : ∑ i, ‖aVec n m i‖ ^ 2 = 1 := eLast_normSq n

theorem aVec_ne_zero (n : ℕ) (m : baseM n dd) : aVec n m ≠ 0 := eLast_ne_zero n

theorem bVec_normSq (n : ℕ) (m : baseM n dd) : ∑ i, ‖bVec n m i‖ ^ 2 = 1 :=
  mem_unitVectors_iff.mp m.1.2

theorem continuous_aVec (n : ℕ) : Continuous (aVec (dd := dd) n) := continuous_const

theorem continuous_bVec (n : ℕ) : Continuous (bVec (dd := dd) n) :=
  continuous_subtype_val.comp continuous_fst

theorem continuous_cVec : Continuous (cVec (dd := dd)) := by
  refine continuous_pi fun p => ?_
  exact (continuous_entry _ _).comp (continuous_apply p.1.1)

/-! ## 3. The three fields take values in the range of `V` -/

/-- **The transverse section is a section of `H`**, at every rank: `H` does not see the
rank at all, so this is the rank-two proof with the base point re-indexed. -/
theorem Hmat_mulVec_cVec (y : baseY dd) : Hmat y *ᵥ cVec y = cVec y := by
  funext p
  obtain ⟨b, k⟩ := p
  rw [Hmat, blockDiagonal'_mulVec]
  show (∑ k', entry (y b.1) k k' * entry (y b.1) k' b.2.succ) = entry (y b.1) k b.2.succ
  exact entry_sum_mul (y b.1) k b.2.succ

theorem Vmat_mulVec_left (n : ℕ) (m : baseM n dd) (u : Fin (n + 1) → ℂ) :
    Vmat n m *ᵥ Sum.elim u (0 : HIdx dd → ℂ) = Sum.elim u (0 : HIdx dd → ℂ) := by
  rw [Vmat, Matrix.fromBlocks_mulVec]
  congr 1 <;> simp

theorem Vmat_mulVec_right (n : ℕ) (m : baseM n dd) :
    Vmat n m *ᵥ Sum.elim (0 : Fin (n + 1) → ℂ) (cVec m.2)
      = Sum.elim (0 : Fin (n + 1) → ℂ) (cVec m.2) := by
  rw [Vmat, Matrix.fromBlocks_mulVec]
  congr 1
  · simp
  · simpa using Hmat_mulVec_cVec m.2

/-! ## 4. The section data at rank `n` -/

variable {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}

/-- **The manuscript's pair is section data for `W_g`, at every rank.**  Every hypothesis
is discharged here except `hGa`, which is Step A's `g e = s`. -/
theorem isMTSectionData_manuscriptData (n : ℕ)
    {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ} {χ : ℝ → ℝ}
    (hch : IsCircleChart y t) (hχ : Continuous χ) (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (hGa : ∀ m : baseM n dd, G m *ᵥ Sum.elim (aVec n m) 0 = Sum.elim (bVec n m) 0) :
    IsMTSectionData (Vmat n) G y t (blockNorth (aVec n))
      (blockSouth (Z := Z) (aVec n) (bVec n) (fun m => cVec m.2) χ y) :=
  isMTSectionData_blockSplit hch (continuous_aVec n) (continuous_bVec n)
    (continuous_cVec.comp' continuous_snd) hχ hχ0 hχ1
    (fun m => Vmat_mulVec_left n m (aVec n m)) (fun m => Vmat_mulVec_left n m (bVec n m))
    (fun m => Vmat_mulVec_right n m) hGa

/-! ## 5. The single zero at rank `n` -/

/-- The point of `S^{2n+1}` antipodal to `e_last`. -/
def negELast (n : ℕ) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨fun i => -eLast n i, by
    rw [mem_unitVectors_iff]
    simpa using eLast_normSq n⟩

/-- The transverse section vanishes exactly at the base point of `Y`. -/
theorem cVec_eq_zero_iff (w : baseY dd) : cVec w = 0 ↔ w = baseYPoint dd := by
  constructor
  · intro h
    funext j
    refine (tautColSection_eq_zero_iff (w j)).mp fun i k => ?_
    have := congrFun h (⟨⟨j, i⟩, k⟩ : HIdx dd)
    simpa using this
  · intro h
    funext p
    have hj : w p.1.1 = basePoint (dd p.1.1) := by rw [h]; rfl
    have := (tautColSection_eq_zero_iff (w p.1.1)).mpr hj p.1.2 p.2
    simpa using this

/-- The trivial-block condition of the zero locus says the sphere coordinate is antipodal
to `e_last`. -/
theorem bVec_eq_neg_aVec_iff (n : ℕ) (m : baseM n dd) :
    bVec n m = -aVec n m ↔ m.1 = negELast n := by
  constructor
  · intro h
    refine Subtype.ext (funext fun i => ?_)
    have := congrFun h i
    simpa [bVec, aVec, negELast] using this
  · intro h
    funext i
    have hi : (m.1 : Fin (n + 1) → ℂ) i = -eLast n i := by rw [h]; rfl
    simpa [bVec, aVec] using hi

/-- **Exactly one zero, at every rank.**  Over `S¹ × S^{2n+1} × Y` the manuscript's
section of the mapping torus vanishes at `p` if and only if `p` is the south pole of the
circle paired with the single base point `(-e_last, (basePoint)ⱼ)`. -/
theorem manuscriptSection_eq_zero_iff_concrete (n : ℕ)
    {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ} {χ : ℝ → ℝ} (hch : IsCircleChart y t)
    (hd : IsMTSectionData (Vmat n) G y t (blockNorth (aVec n))
      (blockSouth (Z := Z) (aVec n) (bVec n) (fun m => cVec m.2) χ y))
    (hχhalf : χ (1 / 2 : ℝ) = 1) (p : Z × baseM n dd) :
    mtSection (Vmat n) G y t (blockNorth (aVec n))
        (blockSouth (aVec n) (bVec n) (fun m => cVec m.2) χ y) p = 0
      ↔ (t p.1 = -1 ∧ y p.1 = 0 ∧ p.2.1 = negELast n ∧ p.2.2 = baseYPoint dd) := by
  rw [mtSection_manuscript_eq_zero_iff hch hd (aVec_ne_zero n) (aVec_normSq n)
    (bVec_normSq n) hχhalf p]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (bVec_eq_neg_aVec_iff n p.2).mp h3, (cVec_eq_zero_iff p.2.2).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (bVec_eq_neg_aVec_iff n p.2).mpr h3, (cVec_eq_zero_iff p.2.2).mpr h4⟩

/-! ## 6. The two complements, and Step A's output, at rank `n` -/

/-- `s sᴴ`, the rank-one projection onto the tautological line of `S^{2n+1}`, sitting in
the trivial block of `V`. -/
def sProj (n : ℕ) (m : baseM n dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Matrix.fromBlocks (rankOneProj (bVec n m)) 0 0 0

/-- `e eᴴ`, the rank-one projection onto the constant line `ℂ e_last`. -/
def eProj (n : ℕ) (_m : baseM n dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Matrix.fromBlocks (rankOneProj (eLast n)) 0 0 0

/-- `F ⊕ H`, the complement of the section `s` in `V`. -/
def FHmat (n : ℕ) (m : baseM n dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Vmat n m - sProj n m

/-- `𝟏^n ⊕ H`, the complement of the section `e` in `V`. -/
def EHmat (n : ℕ) (m : baseM n dd) : Matrix (VIdx n dd) (VIdx n dd) ℂ :=
  Vmat n m - eProj n m

/-- `F ⊕ H` really is `(𝟏^{n+1} − x xᴴ) ⊕ H`; the first block is the analysis layer's
`STW59.Gen.Fproj n` evaluated at the point of `S^{2n+1}`. -/
theorem FHmat_eq_fromBlocks (n : ℕ) (m : baseM n dd) :
    FHmat n m = Matrix.fromBlocks (1 - rankOneProj (bVec n m)) 0 0 (Hmat m.2) := by
  rw [FHmat, Vmat, sProj]
  ext p q
  cases p <;> cases q <;> simp [Matrix.sub_apply]

/-- `𝟏^n ⊕ H` really is `(𝟏^{n+1} − e eᴴ) ⊕ H`. -/
theorem EHmat_eq_fromBlocks (n : ℕ) (m : baseM n dd) :
    EHmat n m = Matrix.fromBlocks (1 - rankOneProj (eLast n)) 0 0 (Hmat m.2) := by
  rw [EHmat, Vmat, eProj]
  ext p q
  cases p <;> cases q <;> simp [Matrix.sub_apply]

/-- **What Step A produces, at rank `n`.**  A continuous unitary of the whole matrix
algebra which preserves `V` and carries the section `e` to the section `s`. -/
def HasStepAUnitary (n : ℕ) (dd : Fin ℓ → ℕ) : Prop :=
  ∃ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G ∧
    (∀ m, IsCornerUnitary (Vmat n m) (G m)) ∧
    (∀ m, G m *ᵥ Sum.elim (aVec n m) 0 = Sum.elim (bVec n m) 0)

end Gen

/-! ## 7. The rank-two bridges

Every rank-two name of `LIXSectionManuscript.lean` and `LemmaTwoStatement.lean` is its own
`Gen` declaration at `n = 2`, **definitionally**.  Each bridge below is `rfl`, which is
the point: `Fin 3` is `Fin (2 + 1)`, `(2 : Fin 3)` is `Fin.last 2`, and no `cast`, no
`Equiv` and no re-proof stands between the fixed-rank layer and the generic one.  Nothing
in the existing closure needs to change for `Gen` to exist. -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem VIdx_eq_gen (dd : Fin ℓ → ℕ) : VIdx dd = Gen.VIdx 2 dd := rfl

theorem baseM_eq_gen (dd : Fin ℓ → ℕ) : baseM dd = Gen.baseM 2 dd := rfl

theorem Hmat_eq_gen (m : baseM dd) : Hmat m = Gen.Hmat m.2 := rfl

theorem Vmat_eq_gen (m : baseM dd) : Vmat m = Gen.Vmat 2 m := rfl

theorem eThree_eq_gen : eThree = Gen.eLast 2 := rfl

theorem eThree_eq_ePole : eThree = LIX.Gen.ePole 2 := rfl

theorem aVec_eq_gen (m : baseM dd) : aVec m = Gen.aVec 2 m := rfl

theorem bVec_eq_gen (m : baseM dd) : bVec m = Gen.bVec 2 m := rfl

theorem cVec_eq_gen (m : baseM dd) : cVec m = Gen.cVec m.2 := rfl

theorem negEThree_eq_gen : negEThree = Gen.negELast 2 := rfl

theorem sProj_eq_gen (m : baseM dd) : sProj m = Gen.sProj 2 m := rfl

theorem eProj_eq_gen (m : baseM dd) : eProj m = Gen.eProj 2 m := rfl

theorem FHmat_eq_gen (m : baseM dd) : FHmat m = Gen.FHmat 2 m := rfl

theorem EHmat_eq_gen (m : baseM dd) : EHmat m = Gen.EHmat 2 m := rfl

theorem hasStepAUnitary_eq_gen (dd : Fin ℓ → ℕ) :
    HasStepAUnitary dd = Gen.HasStepAUnitary 2 dd := rfl

end GroupApproximation.CharClass
