import GroupApproximation.Analysis.LIXLemmaTwoPropGeneric
import GroupApproximation.Analysis.LIXLemmaSixHIdx

/-!
# The manuscript's `H` and the tower's `H` are the same projection, at every rank

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

`Analysis/LIXLemmaSixHIdx.lean` identifies the manuscript's `H`, indexed by the sigma type
`CharClass.HIdx (lixDD j)`, with the tower's `H`, built by the iterated sum
`STW59.HIdx (j+1) = STW59.HIdx j ⊕ NIdx j`, at rank two.  This file does the same at rank
`n`, and `§4` records that the rank-two maps are the `n = 2` instances.

## `H` does not see the rank, but its two presentations do

The block bundle `H = ⊕_{i<j} L_{i+1}^{⊕ r_i}` lives over `Y` alone and involves the
sphere factor nowhere, so nothing in this file changes shape with `n`.  What *does* change
is that both index types are built from `stageRank n`, so every declaration below carries
`n` as a parameter even though no statement is about the rank.

Two simplifications over the rank-two file, both consequences of
`CharClass/LIXShapeGeneric.lean` re-indexing `Hmat` by the point of `Y` alone:

* `hMatY` is `CharClass.Gen.Hmat` outright, so it needs no `Classical.arbitrary` point of
  the sphere and, with it, no `Nonempty` instance;
* `continuous_hMatY` is `CharClass.Gen.continuous_Hmat` outright, with no composition
  against a constant first factor.

## Why this layer is safe to write before the renormalised generator

The renormalised-generator redesign changes the **trivial block** — the section, the
generator, the winding — and touches `H` nowhere.  So the identification proved here is
needed by the Corollary-4 chain in either form, and generalising it now cannot be
invalidated by the `k`-indexed rebuild.

## Main results

* `Gen.hMatY` — the manuscript's `H` over `Y` alone, at rank `n`.
* `Gen.hIdxEquiv` — the reindexing of the two `H`-index types.
* `Gen.hMatY_hIdxTo`, `Gen.hMatY_reindex` — **the two projections agree**, at every rank.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix Kronecker

set_option linter.unusedSectionVars false

noncomputable section

namespace Gen

/-! ## 1. The manuscript's `H` over `Y` alone, at rank `n` -/

/-- The manuscript's `H` at stage `j` of the rank-`n` tower, as a matrix over `Y_j` alone.
`CharClass.Gen.Hmat` is already indexed by the point of `Y`, so this is a rename. -/
def hMatY (n j : ℕ) (y : STW59.Gen.baseY n j) :
    Matrix (CharClass.HIdx (lixDD n j)) (CharClass.HIdx (lixDD n j)) ℂ :=
  CharClass.Gen.Hmat (dd := lixDD n j) y

theorem hMat_eq_hMatY (n j : ℕ) (m : CharClass.Gen.baseM n (lixDD n j)) :
    CharClass.Gen.Hmat m.2 = hMatY n j m.2 := rfl

theorem continuous_hMatY (n j : ℕ) : Continuous (hMatY n j) :=
  CharClass.Gen.continuous_Hmat

theorem isStarProjection_hMatY (n j : ℕ) (y : STW59.Gen.baseY n j) :
    IsStarProjection (hMatY n j y) :=
  CharClass.Gen.isStarProjection_Hmat _

theorem hMatY_mul_self (n j : ℕ) (y : STW59.Gen.baseY n j) :
    hMatY n j y * hMatY n j y = hMatY n j y :=
  (isStarProjection_hMatY n j y).isIdempotentElem.eq

theorem conjTranspose_hMatY (n j : ℕ) (y : STW59.Gen.baseY n j) :
    (hMatY n j y)ᴴ = hMatY n j y := by
  have h : star (hMatY n j y) = hMatY n j y :=
    (isStarProjection_hMatY n j y).isSelfAdjoint.star_eq
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The blocks of the manuscript's `H`, named so that the entry lemmas below are
first-order rewrites. -/
def hBlkMat (n j : ℕ) (y : STW59.Gen.baseY n j) (b : CharClass.HBlk (lixDD n j)) :
    Matrix (Fin (lixDD n j b.1 + 1)) (Fin (lixDD n j b.1 + 1)) ℂ :=
  Matrix.of fun p p' => AlgTop.CPn.entry (y b.1) p p'

theorem hMatY_eq_blockDiagonal' (n j : ℕ) (y : STW59.Gen.baseY n j) :
    hMatY n j y = Matrix.blockDiagonal' (hBlkMat n j y) := rfl

theorem hMatY_apply_eq (n j : ℕ) (y : STW59.Gen.baseY n j) (i : Fin j)
    (k : Fin (lixDD n j i)) (p p' : Fin (lixDD n j i + 1)) :
    hMatY n j y ⟨⟨i, k⟩, p⟩ ⟨⟨i, k⟩, p'⟩ = AlgTop.CPn.entry (y i) p p' :=
  Matrix.blockDiagonal'_apply_eq (hBlkMat n j y) ⟨i, k⟩ p p'

theorem hMatY_apply_ne (n j : ℕ) (y : STW59.Gen.baseY n j) {i i' : Fin j}
    {k : Fin (lixDD n j i)} {k' : Fin (lixDD n j i')}
    (h : (⟨i, k⟩ : CharClass.HBlk (lixDD n j)) ≠ ⟨i', k'⟩)
    (p : Fin (lixDD n j i + 1)) (p' : Fin (lixDD n j i' + 1)) :
    hMatY n j y ⟨⟨i, k⟩, p⟩ ⟨⟨i', k'⟩, p'⟩ = 0 := by
  rw [hMatY_eq_blockDiagonal']
  exact Matrix.blockDiagonal'_apply_ne (hBlkMat n j y) p p' h

/-! ## 2. The two `H`-index types, at rank `n` -/

/-- The tower's `H`-index at stage `j`, as one of the manuscript's. -/
def hIdxTo (n : ℕ) : (j : ℕ) → STW59.Gen.HIdx n j → CharClass.HIdx (lixDD n j)
  | 0 => fun a => a.elim
  | (j + 1) => fun a =>
      match (a : STW59.Gen.HIdx n j ⊕ STW59.Gen.NIdx n j) with
      | Sum.inl a' =>
          ⟨⟨Fin.castSucc (hIdxTo n j a').1.1, (hIdxTo n j a').1.2⟩, (hIdxTo n j a').2⟩
      | Sum.inr kp => ⟨⟨Fin.last j, kp.1⟩, kp.2⟩

theorem hIdxTo_inl (n j : ℕ) (a : STW59.Gen.HIdx n j) :
    hIdxTo n (j + 1) (Sum.inl a)
      = ⟨⟨Fin.castSucc (hIdxTo n j a).1.1, (hIdxTo n j a).1.2⟩, (hIdxTo n j a).2⟩ := rfl

theorem hIdxTo_inr (n j : ℕ) (kp : STW59.Gen.NIdx n j) :
    hIdxTo n (j + 1) (Sum.inr kp) = ⟨⟨Fin.last j, kp.1⟩, kp.2⟩ := rfl

/-- The manuscript's `H`-index at stage `j`, as one of the tower's. -/
def hIdxFrom (n : ℕ) : (j : ℕ) → CharClass.HIdx (lixDD n j) → STW59.Gen.HIdx n j
  | 0 => fun b => b.1.1.elim0
  | (j + 1) => fun b =>
      Fin.lastCases
        (motive := fun i : Fin (j + 1) =>
          Fin (STW59.Gen.stageRank n (i : ℕ)) → Fin (STW59.Gen.stageRank n (i : ℕ) + 1) →
            STW59.Gen.HIdx n (j + 1))
        (fun k p => (Sum.inr (k, p) : STW59.Gen.HIdx n j ⊕ STW59.Gen.NIdx n j))
        (fun i k p =>
          (Sum.inl (hIdxFrom n j ⟨⟨i, k⟩, p⟩) : STW59.Gen.HIdx n j ⊕ STW59.Gen.NIdx n j))
        b.1.1 b.1.2 b.2

theorem hIdxFrom_hIdxTo (n : ℕ) :
    ∀ (j : ℕ) (a : STW59.Gen.HIdx n j), hIdxFrom n j (hIdxTo n j a) = a
  | 0 => fun a => a.elim
  | (j + 1) => fun a => by
      cases a with
      | inl a' =>
          rw [hIdxTo_inl]
          simp only [hIdxFrom, Fin.lastCases_castSucc]
          exact congrArg Sum.inl (hIdxFrom_hIdxTo n j a')
      | inr kp =>
          rw [hIdxTo_inr]
          simp only [hIdxFrom, Fin.lastCases_last]

theorem hIdxTo_hIdxFrom (n : ℕ) :
    ∀ (j : ℕ) (b : CharClass.HIdx (lixDD n j)), hIdxTo n j (hIdxFrom n j b) = b
  | 0 => fun b => b.1.1.elim0
  | (j + 1) => fun b => by
      obtain ⟨⟨i, k⟩, p⟩ := b
      revert k p
      refine Fin.lastCases
        (motive := fun i : Fin (j + 1) => ∀ (k : Fin (STW59.Gen.stageRank n (i : ℕ)))
          (p : Fin (STW59.Gen.stageRank n (i : ℕ) + 1)),
          hIdxTo n (j + 1) (hIdxFrom n (j + 1) ⟨⟨i, k⟩, p⟩) = ⟨⟨i, k⟩, p⟩) ?_ ?_ i
      · intro k p
        simp only [hIdxFrom, Fin.lastCases_last]
        rw [hIdxTo_inr]
      · intro i' k p
        simp only [hIdxFrom, Fin.lastCases_castSucc]
        rw [hIdxTo_inl, hIdxTo_hIdxFrom n j ⟨⟨i', k⟩, p⟩]

/-- **The reindexing of the two `H`-index types**, at rank `n`. -/
def hIdxEquiv (n j : ℕ) : STW59.Gen.HIdx n j ≃ CharClass.HIdx (lixDD n j) where
  toFun := hIdxTo n j
  invFun := hIdxFrom n j
  left_inv := hIdxFrom_hIdxTo n j
  right_inv := hIdxTo_hIdxFrom n j

@[simp] theorem hIdxEquiv_apply (n j : ℕ) (a : STW59.Gen.HIdx n j) :
    hIdxEquiv n j a = hIdxTo n j a := rfl

/-! ## 3. The two projections agree, at rank `n` -/

/-- Weakening a block index does not change the entry. -/
theorem hMatY_castSucc (n j : ℕ) (y : STW59.Gen.baseY n (j + 1))
    (u v : CharClass.HIdx (lixDD n j)) :
    hMatY n (j + 1) y ⟨⟨Fin.castSucc u.1.1, u.1.2⟩, u.2⟩
        ⟨⟨Fin.castSucc v.1.1, v.1.2⟩, v.2⟩
      = hMatY n j (fun l : Fin j => y (Fin.castSucc l)) u v := by
  obtain ⟨⟨i, k⟩, p⟩ := u
  obtain ⟨⟨i', k'⟩, p'⟩ := v
  rcases eq_or_ne i i' with rfl | hi
  · rcases eq_or_ne k k' with rfl | hk
    · rw [hMatY_apply_eq n (j + 1) y (Fin.castSucc i) k p p',
        hMatY_apply_eq n j (fun l : Fin j => y (Fin.castSucc l)) i k p p']
    · have hb : (⟨Fin.castSucc i, k⟩ : CharClass.HBlk (lixDD n (j + 1)))
          ≠ ⟨Fin.castSucc i, k'⟩ := by
        intro hc
        injection hc with _ h2
        exact hk h2
      have hb' : (⟨i, k⟩ : CharClass.HBlk (lixDD n j)) ≠ ⟨i, k'⟩ := by
        intro hc
        injection hc with _ h2
        exact hk h2
      rw [hMatY_apply_ne n (j + 1) y hb,
        hMatY_apply_ne n j (fun l : Fin j => y (Fin.castSucc l)) hb']
  · have hb : (⟨Fin.castSucc i, k⟩ : CharClass.HBlk (lixDD n (j + 1)))
        ≠ ⟨Fin.castSucc i', k'⟩ :=
      fun hc => hi (Fin.castSucc_injective j (congrArg Sigma.fst hc))
    have hb' : (⟨i, k⟩ : CharClass.HBlk (lixDD n j)) ≠ ⟨i', k'⟩ :=
      fun hc => hi (congrArg Sigma.fst hc)
    rw [hMatY_apply_ne n (j + 1) y hb,
      hMatY_apply_ne n j (fun l : Fin j => y (Fin.castSucc l)) hb']

/-- The newest block of `H`, evaluated. -/
theorem matEval_newBlockY (n j : ℕ) (y : STW59.Gen.baseY n (j + 1))
    (k k' : Fin (STW59.Gen.stageRank n j)) (p p' : Fin (STW59.Gen.stageRank n j + 1)) :
    STW59.matEval y (STW59.Gen.newBlockY n j) (k, p) (k', p')
      = if k = k' then AlgTop.CPn.entry (y (Fin.last j)) p p' else 0 := by
  have h : STW59.matEval y (STW59.Gen.newBlockY n j) (k, p) (k', p')
      = ((1 : Matrix (Fin (STW59.Gen.stageRank n j)) (Fin (STW59.Gen.stageRank n j))
            C(STW59.Gen.baseY n (j + 1), ℂ)) k k') y
          * (STW59.Gen.newLineY n j p p') y := rfl
  rw [h, Matrix.one_apply]
  split_ifs with hk
  · rw [ContinuousMap.one_apply, one_mul]
    rfl
  · rw [ContinuousMap.zero_apply, zero_mul]

/-- **The manuscript's `H` is the tower's `H`**, entrywise through the reindexing, at every
rank. -/
theorem hMatY_hIdxTo (n : ℕ) : ∀ (j : ℕ) (y : STW59.Gen.baseY n j) (a b : STW59.Gen.HIdx n j),
    hMatY n j y (hIdxTo n j a) (hIdxTo n j b) = STW59.matEval y (STW59.Gen.HprojY n j) a b
  | 0, _, a, _ => a.elim
  | (j + 1), y, a, b => by
      cases a with
      | inl a' =>
          cases b with
          | inl b' =>
              rw [hIdxTo_inl, hIdxTo_inl, hMatY_castSucc,
                hMatY_hIdxTo n j (fun l : Fin j => y (Fin.castSucc l)) a' b']
              rfl
          | inr kp =>
              have hne : (⟨Fin.castSucc (hIdxTo n j a').1.1, (hIdxTo n j a').1.2⟩
                  : CharClass.HBlk (lixDD n (j + 1))) ≠ ⟨Fin.last j, kp.1⟩ :=
                fun hc => Fin.castSucc_ne_last _ (congrArg Sigma.fst hc)
              rw [hIdxTo_inl, hIdxTo_inr, hMatY_apply_ne n (j + 1) y hne]
              rfl
      | inr kp =>
          cases b with
          | inl b' =>
              have hne : (⟨Fin.last j, kp.1⟩ : CharClass.HBlk (lixDD n (j + 1)))
                  ≠ ⟨Fin.castSucc (hIdxTo n j b').1.1, (hIdxTo n j b').1.2⟩ :=
                fun hc => Fin.castSucc_ne_last _ (congrArg Sigma.fst hc).symm
              rw [hIdxTo_inr, hIdxTo_inl, hMatY_apply_ne n (j + 1) y hne]
              rfl
          | inr kp' =>
              obtain ⟨k, p⟩ := kp
              obtain ⟨k', p'⟩ := kp'
              rw [hIdxTo_inr, hIdxTo_inr]
              show hMatY n (j + 1) y ⟨⟨Fin.last j, k⟩, p⟩ ⟨⟨Fin.last j, k'⟩, p'⟩
                = STW59.matEval y (STW59.Gen.newBlockY n j) (k, p) (k', p')
              rw [matEval_newBlockY]
              rcases eq_or_ne k k' with rfl | hk
              · rw [if_pos rfl, hMatY_apply_eq n (j + 1) y (Fin.last j) k p p']
              · have hb : (⟨Fin.last j, k⟩ : CharClass.HBlk (lixDD n (j + 1)))
                    ≠ ⟨Fin.last j, k'⟩ := by
                  intro hc
                  injection hc with _ h2
                  exact hk h2
                rw [if_neg hk, hMatY_apply_ne n (j + 1) y hb]

/-- **The manuscript's `H` is the tower's `H`**, as matrices, at every rank. -/
theorem hMatY_reindex (n j : ℕ) (y : STW59.Gen.baseY n j) :
    hMatY n j y
      = Matrix.reindex (hIdxEquiv n j) (hIdxEquiv n j)
          (STW59.matEval y (STW59.Gen.HprojY n j)) := by
  refine Matrix.ext fun p q => ?_
  obtain ⟨a, rfl⟩ := (hIdxEquiv n j).surjective p
  obtain ⟨b, rfl⟩ := (hIdxEquiv n j).surjective q
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact hMatY_hIdxTo n j y a b

end Gen

/-! ## 4. The rank-two bridge, and the one that is deliberately absent

`hMatY` is a `rfl`: the rank-two definition feeds `CharClass.Hmat` a `Classical.arbitrary`
point of `S⁵` in the first factor and `CharClass.Gen.Hmat` takes no first factor at all,
but `Hmat` ignores the sphere coordinate, so the two terms are the same after the pair
projection reduces.

`hIdxTo`, `hIdxFrom` and `hIdxEquiv` get **no** bridge here, and that is a decision rather
than an omission.  Unlike every bridge in `CharClass/LIXShapeGeneric.lean`, these would not
be `rfl`: the rank-two file compiles its own structural recursion on `j`, so identifying it
with this file's is a theorem **by induction on `j`**, not a definitional unfolding.  It is
four lines of `hIdxTo_inl`/`hIdxTo_inr` rewriting, and the closing step lands on the
reducible-transparency `rfl` that `rw` inserts, across `lixDD j` versus `Gen.lixDD 2 j` —
which is exactly the shape that costs a probe round.  Nothing consumes it yet: the only
consumer would be a port of the Corollary-4 chain, which will restate the reindexing at
rank `n` outright rather than route through the rank-two maps.  It gets written when a
consumer asks for it. -/

theorem hMatY_eq_gen (j : ℕ) (y : STW59.baseY j) : hMatY j y = Gen.hMatY 2 j y := rfl

end

end LIX
end GroupApproximation
