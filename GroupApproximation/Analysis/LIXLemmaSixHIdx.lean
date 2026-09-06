import GroupApproximation.Analysis.LIXLemmaTwoProp

/-!
# The manuscript's `H` and the tower's `H` are the same projection

Lemma 2 lives over `M = S⁵ × Y_j` with the block bundle
`H = ⊕_{i<j} L_{i+1}^{⊕ r_i}` indexed by the manuscript's *sigma* type
`CharClass.HIdx (lixDD j) = Σ (i, k) : Σ i : Fin j, Fin r_i, Fin (r_i + 1)`, while the
C⋆-tower builds the same bundle by the iterated sum
`STW59.HIdx (j+1) = STW59.HIdx j ⊕ NIdx j`.  The two index types are equivalent but not
equal, and Corollary 4 has to move a unitary of the corner from the second presentation to
the first.

This file supplies the equivalence and the identification of the projections:
`hIdxEquiv j` is the reindexing, and `hMatY_reindex` says that the manuscript's `Hmat` is
the tower's `HprojY` read through it.  Everything is proved by the same recursion the two
sides are defined by, and the only step with content is `hMatY_castSucc`: weakening a
block index of the manuscript's `H` does not change the entry, because `blockDiagonal'` is
diagonal in the block index and `Fin.castSucc` is injective.

## Main results

* `hMatY` — the manuscript's `H` as a matrix over `Y_j` alone, with `hMat_eq_hMatY`.
* `hIdxEquiv` — the reindexing of the `H`-index types.
* `hMatY_hIdxTo`, `hMatY_reindex` — **the two projections agree**.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix Kronecker

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The manuscript's `H` over `Y` alone -/

/-- The manuscript's `H` at stage `j`, as a matrix over `Y_j` alone: `Hmat` does not use
the `S⁵` coordinate, so any point of it will do. -/
def hMatY (j : ℕ) (y : STW59.baseY j) :
    Matrix (CharClass.HIdx (lixDD j)) (CharClass.HIdx (lixDD j)) ℂ :=
  CharClass.Hmat (dd := lixDD j) (Classical.arbitrary _, y)

theorem hMat_eq_hMatY (j : ℕ) (m : CharClass.baseM (lixDD j)) :
    CharClass.Hmat m = hMatY j m.2 := rfl

theorem continuous_hMatY (j : ℕ) : Continuous (hMatY j) :=
  CharClass.continuous_Hmat.comp (continuous_const.prodMk continuous_id)

theorem isStarProjection_hMatY (j : ℕ) (y : STW59.baseY j) :
    IsStarProjection (hMatY j y) :=
  CharClass.isStarProjection_Hmat _

theorem hMatY_mul_self (j : ℕ) (y : STW59.baseY j) :
    hMatY j y * hMatY j y = hMatY j y :=
  (isStarProjection_hMatY j y).isIdempotentElem.eq

theorem conjTranspose_hMatY (j : ℕ) (y : STW59.baseY j) :
    (hMatY j y)ᴴ = hMatY j y := by
  have h : star (hMatY j y) = hMatY j y := (isStarProjection_hMatY j y).isSelfAdjoint.star_eq
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The blocks of the manuscript's `H`, named so that the entry lemmas below are
first-order rewrites. -/
def hBlkMat (j : ℕ) (y : STW59.baseY j) (b : CharClass.HBlk (lixDD j)) :
    Matrix (Fin (lixDD j b.1 + 1)) (Fin (lixDD j b.1 + 1)) ℂ :=
  Matrix.of fun p p' => AlgTop.CPn.entry (y b.1) p p'

theorem hMatY_eq_blockDiagonal' (j : ℕ) (y : STW59.baseY j) :
    hMatY j y = Matrix.blockDiagonal' (hBlkMat j y) := rfl

theorem hMatY_apply_eq (j : ℕ) (y : STW59.baseY j) (i : Fin j) (k : Fin (lixDD j i))
    (p p' : Fin (lixDD j i + 1)) :
    hMatY j y ⟨⟨i, k⟩, p⟩ ⟨⟨i, k⟩, p'⟩ = AlgTop.CPn.entry (y i) p p' :=
  Matrix.blockDiagonal'_apply_eq (hBlkMat j y) ⟨i, k⟩ p p'

theorem hMatY_apply_ne (j : ℕ) (y : STW59.baseY j) {i i' : Fin j} {k : Fin (lixDD j i)}
    {k' : Fin (lixDD j i')} (h : (⟨i, k⟩ : CharClass.HBlk (lixDD j)) ≠ ⟨i', k'⟩)
    (p : Fin (lixDD j i + 1)) (p' : Fin (lixDD j i' + 1)) :
    hMatY j y ⟨⟨i, k⟩, p⟩ ⟨⟨i', k'⟩, p'⟩ = 0 := by
  rw [hMatY_eq_blockDiagonal']
  exact Matrix.blockDiagonal'_apply_ne (hBlkMat j y) p p' h

/-! ## 2. The two `H`-index types -/

/-- The tower's `H`-index at stage `j`, as one of the manuscript's. -/
def hIdxTo : (j : ℕ) → STW59.HIdx j → CharClass.HIdx (lixDD j)
  | 0 => fun a => a.elim
  | (j + 1) => fun a =>
      match (a : STW59.HIdx j ⊕ STW59.NIdx j) with
      | Sum.inl a' =>
          ⟨⟨Fin.castSucc (hIdxTo j a').1.1, (hIdxTo j a').1.2⟩, (hIdxTo j a').2⟩
      | Sum.inr kp => ⟨⟨Fin.last j, kp.1⟩, kp.2⟩

theorem hIdxTo_inl (j : ℕ) (a : STW59.HIdx j) :
    hIdxTo (j + 1) (Sum.inl a)
      = ⟨⟨Fin.castSucc (hIdxTo j a).1.1, (hIdxTo j a).1.2⟩, (hIdxTo j a).2⟩ := rfl

theorem hIdxTo_inr (j : ℕ) (kp : STW59.NIdx j) :
    hIdxTo (j + 1) (Sum.inr kp) = ⟨⟨Fin.last j, kp.1⟩, kp.2⟩ := rfl

/-- The manuscript's `H`-index at stage `j`, as one of the tower's. -/
def hIdxFrom : (j : ℕ) → CharClass.HIdx (lixDD j) → STW59.HIdx j
  | 0 => fun b => b.1.1.elim0
  | (j + 1) => fun b =>
      Fin.lastCases
        (motive := fun i : Fin (j + 1) =>
          Fin (STW59.stageRank (i : ℕ)) → Fin (STW59.stageRank (i : ℕ) + 1) →
            STW59.HIdx (j + 1))
        (fun k p => (Sum.inr (k, p) : STW59.HIdx j ⊕ STW59.NIdx j))
        (fun i k p => (Sum.inl (hIdxFrom j ⟨⟨i, k⟩, p⟩) : STW59.HIdx j ⊕ STW59.NIdx j))
        b.1.1 b.1.2 b.2

theorem hIdxFrom_hIdxTo : ∀ (j : ℕ) (a : STW59.HIdx j), hIdxFrom j (hIdxTo j a) = a
  | 0 => fun a => a.elim
  | (j + 1) => fun a => by
      cases a with
      | inl a' =>
          rw [hIdxTo_inl]
          simp only [hIdxFrom, Fin.lastCases_castSucc]
          exact congrArg Sum.inl (hIdxFrom_hIdxTo j a')
      | inr kp =>
          rw [hIdxTo_inr]
          simp only [hIdxFrom, Fin.lastCases_last]

theorem hIdxTo_hIdxFrom : ∀ (j : ℕ) (b : CharClass.HIdx (lixDD j)), hIdxTo j (hIdxFrom j b) = b
  | 0 => fun b => b.1.1.elim0
  | (j + 1) => fun b => by
      obtain ⟨⟨i, k⟩, p⟩ := b
      revert k p
      refine Fin.lastCases
        (motive := fun i : Fin (j + 1) => ∀ (k : Fin (STW59.stageRank (i : ℕ)))
          (p : Fin (STW59.stageRank (i : ℕ) + 1)),
          hIdxTo (j + 1) (hIdxFrom (j + 1) ⟨⟨i, k⟩, p⟩) = ⟨⟨i, k⟩, p⟩) ?_ ?_ i
      · intro k p
        simp only [hIdxFrom, Fin.lastCases_last]
        rw [hIdxTo_inr]
      · intro i' k p
        simp only [hIdxFrom, Fin.lastCases_castSucc]
        rw [hIdxTo_inl, hIdxTo_hIdxFrom j ⟨⟨i', k⟩, p⟩]

/-- **The reindexing of the two `H`-index types.** -/
def hIdxEquiv (j : ℕ) : STW59.HIdx j ≃ CharClass.HIdx (lixDD j) where
  toFun := hIdxTo j
  invFun := hIdxFrom j
  left_inv := hIdxFrom_hIdxTo j
  right_inv := hIdxTo_hIdxFrom j

@[simp] theorem hIdxEquiv_apply (j : ℕ) (a : STW59.HIdx j) : hIdxEquiv j a = hIdxTo j a := rfl

/-! ## 3. The two projections agree -/

/-- Weakening a block index does not change the entry. -/
theorem hMatY_castSucc (j : ℕ) (y : STW59.baseY (j + 1))
    (u v : CharClass.HIdx (lixDD j)) :
    hMatY (j + 1) y ⟨⟨Fin.castSucc u.1.1, u.1.2⟩, u.2⟩ ⟨⟨Fin.castSucc v.1.1, v.1.2⟩, v.2⟩
      = hMatY j (fun l : Fin j => y (Fin.castSucc l)) u v := by
  obtain ⟨⟨i, k⟩, p⟩ := u
  obtain ⟨⟨i', k'⟩, p'⟩ := v
  rcases eq_or_ne i i' with rfl | hi
  · rcases eq_or_ne k k' with rfl | hk
    · rw [hMatY_apply_eq (j + 1) y (Fin.castSucc i) k p p',
        hMatY_apply_eq j (fun l : Fin j => y (Fin.castSucc l)) i k p p']
    · have hb : (⟨Fin.castSucc i, k⟩ : CharClass.HBlk (lixDD (j + 1)))
          ≠ ⟨Fin.castSucc i, k'⟩ := by
        intro hc
        injection hc with _ h2
        exact hk h2
      have hb' : (⟨i, k⟩ : CharClass.HBlk (lixDD j)) ≠ ⟨i, k'⟩ := by
        intro hc
        injection hc with _ h2
        exact hk h2
      rw [hMatY_apply_ne (j + 1) y hb,
        hMatY_apply_ne j (fun l : Fin j => y (Fin.castSucc l)) hb']
  · have hb : (⟨Fin.castSucc i, k⟩ : CharClass.HBlk (lixDD (j + 1)))
        ≠ ⟨Fin.castSucc i', k'⟩ :=
      fun hc => hi (Fin.castSucc_injective j (congrArg Sigma.fst hc))
    have hb' : (⟨i, k⟩ : CharClass.HBlk (lixDD j)) ≠ ⟨i', k'⟩ :=
      fun hc => hi (congrArg Sigma.fst hc)
    rw [hMatY_apply_ne (j + 1) y hb,
      hMatY_apply_ne j (fun l : Fin j => y (Fin.castSucc l)) hb']

/-- The newest block of `H`, evaluated. -/
theorem matEval_newBlockY (j : ℕ) (y : STW59.baseY (j + 1))
    (k k' : Fin (STW59.stageRank j)) (p p' : Fin (STW59.stageRank j + 1)) :
    STW59.matEval y (STW59.newBlockY j) (k, p) (k', p')
      = if k = k' then AlgTop.CPn.entry (y (Fin.last j)) p p' else 0 := by
  have h : STW59.matEval y (STW59.newBlockY j) (k, p) (k', p')
      = ((1 : Matrix (Fin (STW59.stageRank j)) (Fin (STW59.stageRank j))
            C(STW59.baseY (j + 1), ℂ)) k k') y * (STW59.newLineY j p p') y := rfl
  rw [h, Matrix.one_apply]
  split_ifs with hk
  · rw [ContinuousMap.one_apply, one_mul]
    rfl
  · rw [ContinuousMap.zero_apply, zero_mul]

/-- **The manuscript's `H` is the tower's `H`**, entrywise through the reindexing. -/
theorem hMatY_hIdxTo : ∀ (j : ℕ) (y : STW59.baseY j) (a b : STW59.HIdx j),
    hMatY j y (hIdxTo j a) (hIdxTo j b) = STW59.matEval y (STW59.HprojY j) a b
  | 0, _, a, _ => a.elim
  | (j + 1), y, a, b => by
      cases a with
      | inl a' =>
          cases b with
          | inl b' =>
              rw [hIdxTo_inl, hIdxTo_inl, hMatY_castSucc,
                hMatY_hIdxTo j (fun l : Fin j => y (Fin.castSucc l)) a' b']
              rfl
          | inr kp =>
              have hne : (⟨Fin.castSucc (hIdxTo j a').1.1, (hIdxTo j a').1.2⟩
                  : CharClass.HBlk (lixDD (j + 1))) ≠ ⟨Fin.last j, kp.1⟩ :=
                fun hc => Fin.castSucc_ne_last _ (congrArg Sigma.fst hc)
              rw [hIdxTo_inl, hIdxTo_inr, hMatY_apply_ne (j + 1) y hne]
              rfl
      | inr kp =>
          cases b with
          | inl b' =>
              have hne : (⟨Fin.last j, kp.1⟩ : CharClass.HBlk (lixDD (j + 1)))
                  ≠ ⟨Fin.castSucc (hIdxTo j b').1.1, (hIdxTo j b').1.2⟩ :=
                fun hc => Fin.castSucc_ne_last _ (congrArg Sigma.fst hc).symm
              rw [hIdxTo_inr, hIdxTo_inl, hMatY_apply_ne (j + 1) y hne]
              rfl
          | inr kp' =>
              obtain ⟨k, p⟩ := kp
              obtain ⟨k', p'⟩ := kp'
              rw [hIdxTo_inr, hIdxTo_inr]
              show hMatY (j + 1) y ⟨⟨Fin.last j, k⟩, p⟩ ⟨⟨Fin.last j, k'⟩, p'⟩
                = STW59.matEval y (STW59.newBlockY j) (k, p) (k', p')
              rw [matEval_newBlockY]
              rcases eq_or_ne k k' with rfl | hk
              · rw [if_pos rfl, hMatY_apply_eq (j + 1) y (Fin.last j) k p p']
              · have hb : (⟨Fin.last j, k⟩ : CharClass.HBlk (lixDD (j + 1)))
                    ≠ ⟨Fin.last j, k'⟩ := by
                  intro hc
                  injection hc with _ h2
                  exact hk h2
                rw [if_neg hk, hMatY_apply_ne (j + 1) y hb]

/-- **The manuscript's `H` is the tower's `H`**, as matrices. -/
theorem hMatY_reindex (j : ℕ) (y : STW59.baseY j) :
    hMatY j y
      = Matrix.reindex (hIdxEquiv j) (hIdxEquiv j) (STW59.matEval y (STW59.HprojY j)) := by
  refine Matrix.ext fun p q => ?_
  obtain ⟨a, rfl⟩ := (hIdxEquiv j).surjective p
  obtain ⟨b, rfl⟩ := (hIdxEquiv j).surjective q
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact hMatY_hIdxTo j y a b

end

end LIX
end GroupApproximation
