import GroupApproximation.CharClass.BundleLineTriv

/-!
# Complex vector bundles in the projection model, XIX: the one-step comparison

`projIncl` adds a single coordinate, and in the `ι ⊕ Unit` indexing it puts the
old coordinates first (`coordIncl Sum.inl`).  The hyperplane inclusion of
`ℂP^d` puts them last (`shiftMat d = coordIncl Fin.succ`).  Two injections into
the same finite target of the same size differ by a permutation of the target,
and here the permutation is the one-step rotation.

That is `coordIncl_finRotate_mul_castSucc`, and it is the whole comparison at
the matrix level.  A consumer who has a permutation acting on `ℂP^d` -- and who
knows that permuting homogeneous coordinates fixes the degree-two generator --
gets the topological half from it in two lines, with no stabilisation to twice
the dimension and no disjointness of ranges.

## Main declarations

* `sumUnitEquiv` — **the reindexing**, `Fin (d+1) ⊕ Unit ≃ Fin (d+2)`.
* `sumInclLeft_sumUnitEquiv` — under it the block column is `coordIncl castSucc`.
* `finRotate_castSucc` — the rotation carries `castSucc` to `succ`.
* `coordIncl_finRotate_mul_castSucc` — **the comparison**, at the matrix level.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section OneStep

variable {d : ℕ}

/-- **The reindexing.**  `Fin (d+1) ⊕ Unit ≃ Fin (d+2)`, sending the summand to
the first `d+1` coordinates and the `Unit` to the last.  This is the spelling to
use whenever the `ι ⊕ Unit` indexing of `plusOne` has to meet the `Fin (d+2)`
indexing of `ℂP^{d+1}`; do not introduce a second one. -/
def sumUnitEquiv (d : ℕ) : Fin (d + 1) ⊕ Unit ≃ Fin (d + 1 + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin (d + 1))) (Equiv.ofUnique Unit (Fin 1))).trans
    finSumFinEquiv

theorem sumUnitEquiv_inl (d : ℕ) (i : Fin (d + 1)) :
    sumUnitEquiv d (Sum.inl i) = i.castSucc := rfl

theorem sumUnitEquiv_inr (d : ℕ) (u : Unit) :
    sumUnitEquiv d (Sum.inr u) = Fin.last (d + 1) := by
  apply Fin.ext
  simp [sumUnitEquiv, Fin.last]

/-- Under the reindexing the block column is the coordinate inclusion of
`Fin.castSucc`. -/
theorem sumInclLeft_sumUnitEquiv (d : ℕ) :
    sumInclLeft (sumUnitEquiv d)
      = coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1)) := by
  rw [sumInclLeft_eq_coordIncl]
  rfl

/-- **The one-step rotation carries `castSucc` to `succ`.**  No wraparound
occurs, because `castSucc i` is never the last coordinate. -/
theorem finRotate_castSucc (d : ℕ) (i : Fin (d + 1)) :
    finRotate (d + 1 + 1) i.castSucc = i.succ := by
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc, Fin.val_succ]

theorem coordIncl_finRotate_isometry (d : ℕ) :
    (coordIncl (⇑(finRotate (d + 1 + 1))))ᴴ * coordIncl (⇑(finRotate (d + 1 + 1)))
      = (1 : Matrix (Fin (d + 1 + 1)) (Fin (d + 1 + 1)) ℂ) :=
  coordIncl_isometry (finRotate (d + 1 + 1)).injective

theorem coordIncl_finRotate_mul_conjTranspose (d : ℕ) :
    coordIncl (⇑(finRotate (d + 1 + 1))) * (coordIncl (⇑(finRotate (d + 1 + 1))))ᴴ
      = (1 : Matrix (Fin (d + 1 + 1)) (Fin (d + 1 + 1)) ℂ) :=
  coordIncl_mul_conjTranspose_of_bijective (finRotate (d + 1 + 1)).bijective

/-- **The comparison.**  The block column of the `ι ⊕ Unit` indexing, followed
by the one-step rotation, is the hyperplane inclusion's matrix.  Both sides are
`Matrix (Fin (d+2)) (Fin (d+1)) ℂ`, so nothing is cast. -/
theorem coordIncl_finRotate_mul_castSucc (d : ℕ) :
    coordIncl (⇑(finRotate (d + 1 + 1)))
        * coordIncl (Fin.castSucc : Fin (d + 1) → Fin (d + 1 + 1))
      = shiftMat d := by
  rw [coordIncl_mul_coordIncl, shiftMat_def]
  congr 1
  funext i
  exact finRotate_castSucc d i

/-- The same, stated against the block column of the reindexing. -/
theorem coordIncl_finRotate_mul_sumInclLeft (d : ℕ) :
    coordIncl (⇑(finRotate (d + 1 + 1))) * sumInclLeft (sumUnitEquiv d) = shiftMat d := by
  rw [sumInclLeft_sumUnitEquiv, coordIncl_finRotate_mul_castSucc]

end OneStep

end Bundle

end CharClass
end GroupApproximation
