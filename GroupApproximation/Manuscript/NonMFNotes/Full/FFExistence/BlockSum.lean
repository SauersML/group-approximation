import GroupApproximation.Leavitt.ElementaryStabilization

/-!
# Block-diagonal sums of elementary groups

Supporting file for `rem:ff-realization` (`non_mf_group_notes.tex`), first
sentence: a group `P` containing a direct product `P₁ × P₂ × S`.

For finite index types `ι, κ` and a ring `R`, the block-diagonal map
`(g, h) ↦ diag(g, h)` is an injective homomorphism
`EL_ι(R) × EL_κ(R) →* EL_{ι ⊕ κ}(R)` (`blockSum`, `blockSum_injective`),
and iterating it gives `EL_ι × EL_κ × EL_μ ↪ EL_{ι ⊕ (κ ⊕ μ)}`
(`blockSumThree`, `blockSumThree_injective`).

The upper-left inclusion is the repository's `elementaryStabilization`; the
lower-right inclusion is the upper-left one conjugated by the swap
`κ ⊕ ι ≃ ι ⊕ κ` (`rightStabilization`).  The two images commute because they
are supported on complementary blocks.
-/

namespace GroupApproximation.Full.NN08b

noncomputable section

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

/-- The upper-left inclusion, as a matrix: `g ↦ diag(g, 1)`. -/
theorem leftStabilization_val (g : elementaryGroup ι R) :
    ((elementaryStabilization (κ := κ) g : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
        Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      Matrix.fromBlocks ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) 0 0 1 :=
  rfl

/-- The lower-right inclusion `EL_κ(R) → EL_{ι ⊕ κ}(R)`, `h ↦ diag(1, h)`. -/
def rightStabilization : elementaryGroup κ R →* elementaryGroup (ι ⊕ κ) R :=
  (elementaryReindexEquiv (R := R) (Equiv.sumComm κ ι)).toMonoidHom.comp
    (elementaryStabilization (ι := κ) (κ := ι) (R := R))

/-- The lower-right inclusion, as a matrix: `h ↦ diag(1, h)`. -/
theorem rightStabilization_val (h : elementaryGroup κ R) :
    ((rightStabilization (ι := ι) h : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
        Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      Matrix.fromBlocks 1 0 0 ((h : (Matrix κ κ R)ˣ) : Matrix κ κ R) := by
  change (Matrix.fromBlocks ((h : (Matrix κ κ R)ˣ) : Matrix κ κ R)
      (0 : Matrix κ ι R) (0 : Matrix ι κ R) (1 : Matrix ι ι R)).submatrix
        Sum.swap Sum.swap = _
  exact Matrix.fromBlocks_submatrix_sum_swap_sum_swap
    ((h : (Matrix κ κ R)ˣ) : Matrix κ κ R) (0 : Matrix κ ι R)
    (0 : Matrix ι κ R) (1 : Matrix ι ι R)

/-- The upper-left and lower-right blocks commute. -/
theorem stabilization_commute (g : elementaryGroup ι R)
    (h : elementaryGroup κ R) :
    Commute (elementaryStabilization (κ := κ) g)
      (rightStabilization (ι := ι) h) := by
  have hval :
      ((elementaryStabilization (κ := κ) g : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) *
        ((rightStabilization (ι := ι) h : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      ((rightStabilization (ι := ι) h : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) *
        ((elementaryStabilization (κ := κ) g : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) := by
    rw [leftStabilization_val, rightStabilization_val,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
  apply Subtype.ext
  apply Units.ext
  exact hval

/-- **Block-diagonal sum** `EL_ι(R) × EL_κ(R) →* EL_{ι ⊕ κ}(R)`,
`(g, h) ↦ diag(g, h)`. -/
def blockSum : elementaryGroup ι R × elementaryGroup κ R →*
    elementaryGroup (ι ⊕ κ) R :=
  MonoidHom.noncommCoprod (elementaryStabilization (κ := κ))
    (rightStabilization (ι := ι)) stabilization_commute

/-- The block-diagonal sum, as a matrix. -/
theorem blockSum_val (g : elementaryGroup ι R) (h : elementaryGroup κ R) :
    ((blockSum (g, h) : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
        Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      Matrix.fromBlocks ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) 0 0
        ((h : (Matrix κ κ R)ˣ) : Matrix κ κ R) := by
  have hmul :
      ((blockSum (g, h) : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
        ((elementaryStabilization (κ := κ) g : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
            Matrix (ι ⊕ κ) (ι ⊕ κ) R) *
          ((rightStabilization (ι := ι) h : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
            Matrix (ι ⊕ κ) (ι ⊕ κ) R) :=
    rfl
  rw [hmul, leftStabilization_val, rightStabilization_val,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]

/-- The block-diagonal sum is injective. -/
theorem blockSum_injective :
    Function.Injective (blockSum (ι := ι) (κ := κ) (R := R)) := by
  rintro ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ hgh
  have hM :
      ((blockSum (g₁, h₁) : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
        ((blockSum (g₂, h₂) : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) R) :=
    congrArg (fun x : elementaryGroup (ι ⊕ κ) R =>
      ((x : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) : Matrix (ι ⊕ κ) (ι ⊕ κ) R)) hgh
  rw [blockSum_val, blockSum_val] at hM
  obtain ⟨hg, -, -, hh⟩ := Matrix.fromBlocks_inj.mp hM
  have hg' : g₁ = g₂ := Subtype.ext (Units.ext hg)
  have hh' : h₁ = h₂ := Subtype.ext (Units.ext hh)
  rw [hg', hh']

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- **Three-block diagonal sum**
`EL_ι(R) × EL_κ(R) × EL_μ(R) →* EL_{ι ⊕ (κ ⊕ μ)}(R)`. -/
def blockSumThree :
    elementaryGroup ι R × elementaryGroup κ R × elementaryGroup μ R →*
      elementaryGroup (ι ⊕ (κ ⊕ μ)) R :=
  (blockSum (ι := ι) (κ := κ ⊕ μ) (R := R)).comp
    (MonoidHom.prodMap (MonoidHom.id (elementaryGroup ι R))
      (blockSum (ι := κ) (κ := μ) (R := R)))

theorem blockSumThree_apply (a : elementaryGroup ι R)
    (b : elementaryGroup κ R) (c : elementaryGroup μ R) :
    blockSumThree (a, b, c) = blockSum (a, blockSum (b, c)) :=
  rfl

/-- The three-block diagonal sum is injective. -/
theorem blockSumThree_injective :
    Function.Injective
      (blockSumThree (ι := ι) (κ := κ) (μ := μ) (R := R)) := by
  rintro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ habc
  rw [blockSumThree_apply, blockSumThree_apply] at habc
  have h₁ := blockSum_injective habc
  have ha : a₁ = a₂ := congrArg Prod.fst h₁
  have hbc : blockSum (b₁, c₁) = blockSum (b₂, c₂) := congrArg Prod.snd h₁
  have h₂ := blockSum_injective hbc
  have hb : b₁ = b₂ := congrArg Prod.fst h₂
  have hc : c₁ = c₂ := congrArg Prod.snd h₂
  rw [ha, hb, hc]

end

end GroupApproximation.Full.NN08b
