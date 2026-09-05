import GroupApproximation.KTheory.MatrixProjection

/-!
# The reindexing moves: functoriality, commutativity, associativity, unit

`MatrixProjection.lean` supplies the block sum and the two facts that make it
usable: a block sum of projections is a projection, and Murray--von Neumann
equivalence is additive under it and survives reindexing.  What is still
missing before the block sum can be an *addition* is that it is commutative,
associative and unital.

None of the three is an identity of matrices as they stand, because `m + n`
and `n + m`, and `(m + n) + k` and `m + (n + k)`, are different types.  Each is
therefore an identity **up to a reindexing `Equiv`**, and each `Equiv` is
assembled here from `finSumFinEquiv` and the corresponding move on `⊕`
(`Equiv.sumCongr`, `Equiv.sumComm`, `Equiv.sumAssoc`).
`murrayVonNeumannEquiv_submatrix` turns each identity into a move on
Murray--von Neumann classes, which is where they are consumed.

## Shape of the proofs

Every reindexing `Equiv` is pinned by what it does to the two constructors
`Fin.castAdd` and `Fin.natAdd`, and those four (resp. three) `simp` lemmas are
the entire interface.  Each move is then proved by `Fin.addCases` on both
indices, and each leaf is closed by `simp` from the four entry lemmas for
`blockSum`.  No entry arithmetic on `Fin`, no `Nat.add_assoc` transport across
a type, and no permutation matrix appears anywhere.

`blockSum_zero_left` is deliberately absent: `0 + m` is not definitionally `m`
in Lean (`Nat.add` recurses on its second argument), so the left unit law is
not an identity of matrices at all.  It is not needed either -- on the quotient
it follows from `blockSum_zero_right` and `blockSum_comm`.
-/

namespace GroupApproximation
namespace KTheory

open Matrix

variable {A : Type*} {m n k m' n' : ℕ}

/-! ## The remaining two entry lemmas

The two diagonal ones are in `MatrixProjection.lean`; these are the two
off-diagonal blocks, which are zero. -/

section Entries

variable [Zero A]

@[simp]
theorem blockSum_apply_castAdd_natAdd (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) (i : Fin m) (j : Fin n) :
    blockSum p q (Fin.castAdd n i) (Fin.natAdd m j) = 0 := by
  simp [blockSum, Matrix.submatrix_apply]

@[simp]
theorem blockSum_apply_natAdd_castAdd (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) (i : Fin n) (j : Fin m) :
    blockSum p q (Fin.natAdd m i) (Fin.castAdd n j) = 0 := by
  simp [blockSum, Matrix.submatrix_apply]

end Entries

/-! ## The three reindexing equivalences -/

/-- The `Fin`-level image of `Equiv.sumCongr`: reindex the two blocks of a
block sum separately. -/
def finSumCongr (e : Fin m' ≃ Fin m) (f : Fin n' ≃ Fin n) : Fin (m' + n') ≃ Fin (m + n) :=
  finSumFinEquiv.symm.trans ((e.sumCongr f).trans finSumFinEquiv)

/-- The `Fin`-level image of `Equiv.sumComm`: exchange the two blocks. -/
def finSumSwap (m n : ℕ) : Fin (m + n) ≃ Fin (n + m) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin m) (Fin n)).trans finSumFinEquiv)

/-- The `Fin`-level image of `Equiv.sumAssoc`: reassociate three blocks. -/
def finSumAssoc (m n k : ℕ) : Fin (m + n + k) ≃ Fin (m + (n + k)) :=
  (finSumFinEquiv.symm.trans
    ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin k))).trans
      ((Equiv.sumAssoc (Fin m) (Fin n) (Fin k)).trans
        ((Equiv.refl (Fin m)).sumCongr finSumFinEquiv)))).trans finSumFinEquiv

@[simp]
theorem finSumCongr_castAdd (e : Fin m' ≃ Fin m) (f : Fin n' ≃ Fin n) (a : Fin m') :
    finSumCongr e f (Fin.castAdd n' a) = Fin.castAdd n (e a) := by
  simp [finSumCongr]

@[simp]
theorem finSumCongr_natAdd (e : Fin m' ≃ Fin m) (f : Fin n' ≃ Fin n) (b : Fin n') :
    finSumCongr e f (Fin.natAdd m' b) = Fin.natAdd m (f b) := by
  simp [finSumCongr]

@[simp]
theorem finSumSwap_castAdd (a : Fin m) :
    finSumSwap m n (Fin.castAdd n a) = Fin.natAdd n a := by
  simp [finSumSwap, Equiv.sumComm]

@[simp]
theorem finSumSwap_natAdd (b : Fin n) :
    finSumSwap m n (Fin.natAdd m b) = Fin.castAdd m b := by
  simp [finSumSwap, Equiv.sumComm]

@[simp]
theorem finSumAssoc_castAdd_castAdd (a : Fin m) :
    finSumAssoc m n k (Fin.castAdd k (Fin.castAdd n a)) = Fin.castAdd (n + k) a := by
  simp [finSumAssoc]

@[simp]
theorem finSumAssoc_castAdd_natAdd (b : Fin n) :
    finSumAssoc m n k (Fin.castAdd k (Fin.natAdd m b)) = Fin.natAdd m (Fin.castAdd k b) := by
  simp [finSumAssoc]

@[simp]
theorem finSumAssoc_natAdd (c : Fin k) :
    finSumAssoc m n k (Fin.natAdd (m + n) c) = Fin.natAdd m (Fin.natAdd n c) := by
  simp [finSumAssoc]

/-! ## The moves -/

section Moves

variable [Zero A]

/-- **Functoriality of the block sum in both blocks.**  Reindexing the two
summands separately is reindexing the sum along `finSumCongr`. -/
theorem blockSum_submatrix (e : Fin m' ≃ Fin m) (f : Fin n' ≃ Fin n)
    (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) A) :
    (blockSum p q).submatrix (finSumCongr e f) (finSumCongr e f)
      = blockSum (p.submatrix e e) (q.submatrix f f) := by
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b => simp
    | right b => simp
  | right a =>
    induction j using Fin.addCases with
    | left b => simp
    | right b => simp

/-- **The block sum is commutative up to the block swap.** -/
theorem blockSum_comm (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) A) :
    (blockSum p q).submatrix (finSumSwap n m) (finSumSwap n m) = blockSum q p := by
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b => simp
    | right b => simp
  | right a =>
    induction j using Fin.addCases with
    | left b => simp
    | right b => simp

/-- **The block sum is associative up to reassociation.** -/
theorem blockSum_assoc (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) A)
    (r : Matrix (Fin k) (Fin k) A) :
    (blockSum p (blockSum q r)).submatrix (finSumAssoc m n k) (finSumAssoc m n k)
      = blockSum (blockSum p q) r := by
  ext i j
  induction i using Fin.addCases with
  | left u =>
    induction u using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left v =>
        induction v using Fin.addCases with
        | left b => simp
        | right b => simp
      | right v => simp
    | right a =>
      induction j using Fin.addCases with
      | left v =>
        induction v using Fin.addCases with
        | left b => simp
        | right b => simp
      | right v => simp
  | right u =>
    induction j using Fin.addCases with
    | left v =>
      induction v using Fin.addCases with
      | left b => simp
      | right b => simp
    | right v => simp

/-- **The empty block is a right unit.**  This is an honest identity of
matrices: `m + 0` reduces to `m`, so both sides live in the same type. -/
theorem blockSum_zero_right (p : Matrix (Fin m) (Fin m) A) :
    blockSum p (0 : Matrix (Fin 0) (Fin 0) A) = p := by
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b => simpa using blockSum_apply_castAdd_castAdd p (0 : Matrix (Fin 0) (Fin 0) A) a b
    | right b => exact b.elim0
  | right a => exact a.elim0

end Moves

end KTheory
end GroupApproximation
