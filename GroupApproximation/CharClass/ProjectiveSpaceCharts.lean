import GroupApproximation.CharClass.ProjectiveSpaceCover

/-!
# The standard charts of `ℂP^d`

The Mayer–Vietoris computation of `H^*(ℂP^d)` uses one chart and the complement of
a point.  A bundle argument needs something else: a cover by open sets over which
a line bundle is *trivial*, and for the tautological line that is the `d+1`
standard charts `{z : z_{ii} ≠ 0}`.

They are all homeomorphic to the zeroth, by exchanging two homogeneous
coordinates.  Written as a submatrix rather than as conjugation by a permutation
matrix, that exchange is definitional on entries, so hermitianness and
idempotence transport with no computation and the trace is a reindexed sum.

## Main declarations

* `swapMat`, `swapCP` — exchanging the coordinates `0` and `i`, on matrices and on
  `ℂP^d`.
* `chartSetAt`, `isOpen_chartSetAt`, `contractibleSpace_chartSetAt` — the charts.
* `exists_mem_chartSetAt` — **they cover**, because the trace is `1`.
* `chartOpenAt` — the charts as open sets of `CPtop d`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open Matrix TopologicalSpace
open GroupApproximation.STW59

noncomputable section

variable {d : ℕ}

/-! ## 1. Exchanging two homogeneous coordinates -/

/-- Exchange the coordinates `0` and `i` of a matrix. -/
def swapMat (i : Fin (d + 1)) (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  q.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i)

@[simp] theorem swapMat_apply (i : Fin (d + 1))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (a b : Fin (d + 1)) :
    swapMat i q a b = q (Equiv.swap 0 i a) (Equiv.swap 0 i b) := rfl

theorem swapMat_swapMat (i : Fin (d + 1))
    (q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : swapMat i (swapMat i q) = q := by
  ext a b
  show q (Equiv.swap 0 i (Equiv.swap 0 i a)) (Equiv.swap 0 i (Equiv.swap 0 i b)) = q a b
  rw [Equiv.swap_apply_self, Equiv.swap_apply_self]

theorem swapMat_mem_cpSet (i : Fin (d + 1))
    {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hq : q ∈ cpSet d) :
    swapMat i q ∈ cpSet d := by
  obtain ⟨hH, hI, hT⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    show star (q (Equiv.swap 0 i b) (Equiv.swap 0 i a))
      = q (Equiv.swap 0 i a) (Equiv.swap 0 i b)
    exact congrFun (congrFun hH (Equiv.swap 0 i a)) (Equiv.swap 0 i b)
  · show q.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i)
        * q.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i)
      = q.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i)
    rw [Matrix.submatrix_mul_equiv, hI]
  · show (q.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i)).trace = 1
    rw [← hT]
    exact Equiv.sum_comp (Equiv.swap 0 i) (fun b => q b b)

/-- **Exchanging two homogeneous coordinates is a homeomorphism of `ℂP^d`.** -/
def swapCP (i : Fin (d + 1)) : CP d ≃ₜ CP d where
  toFun z := ⟨swapMat i z, swapMat_mem_cpSet i z.2⟩
  invFun z := ⟨swapMat i z, swapMat_mem_cpSet i z.2⟩
  left_inv _ := Subtype.ext (swapMat_swapMat i _)
  right_inv _ := Subtype.ext (swapMat_swapMat i _)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    exact continuous_entry (d := d) (Equiv.swap 0 i a) (Equiv.swap 0 i b)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    exact continuous_entry (d := d) (Equiv.swap 0 i a) (Equiv.swap 0 i b)

@[simp] theorem entry_swapCP (i : Fin (d + 1)) (z : CP d) (a b : Fin (d + 1)) :
    entry (swapCP i z) a b = entry z (Equiv.swap 0 i a) (Equiv.swap 0 i b) := rfl

/-! ## 2. The standard charts -/

/-- The `i`-th standard chart of `ℂP^d`: the lines not contained in the hyperplane
`z_i = 0`. -/
def chartSetAt (i : Fin (d + 1)) : Set (CP d) := {z | entry z i i ≠ 0}

theorem mem_chartSetAt {i : Fin (d + 1)} {z : CP d} :
    z ∈ chartSetAt i ↔ entry z i i ≠ 0 := Iff.rfl

theorem chartSetAt_zero : chartSetAt (0 : Fin (d + 1)) = chartSet d := rfl

theorem isOpen_chartSetAt (i : Fin (d + 1)) : IsOpen (chartSetAt (d := d) i) :=
  (continuous_entry (d := d) i i).isOpen_preimage {0}ᶜ isOpen_compl_singleton

theorem swapCP_mem_chartSet (i : Fin (d + 1)) {z : CP d} (hz : z ∈ chartSetAt i) :
    swapCP i z ∈ chartSet d := by
  rw [mem_chartSet, entry_swapCP, Equiv.swap_apply_left]
  exact hz

theorem swapCP_mem_chartSetAt (i : Fin (d + 1)) {z : CP d} (hz : z ∈ chartSet d) :
    swapCP i z ∈ chartSetAt i := by
  rw [mem_chartSetAt, entry_swapCP, Equiv.swap_apply_right]
  exact hz

/-- **Every standard chart is homeomorphic to the zeroth.** -/
def chartAtHomeo (i : Fin (d + 1)) : ↥(chartSetAt (d := d) i) ≃ₜ ↥(chartSet d) where
  toFun z := ⟨swapCP i (z : CP d), swapCP_mem_chartSet i z.2⟩
  invFun w := ⟨swapCP i (w : CP d), swapCP_mem_chartSetAt i w.2⟩
  left_inv _ := Subtype.ext (Subtype.ext (swapMat_swapMat i _))
  right_inv _ := Subtype.ext (Subtype.ext (swapMat_swapMat i _))
  continuous_toFun :=
    Continuous.subtype_mk ((swapCP i).continuous.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((swapCP i).continuous.comp continuous_subtype_val) _

/-- **Every standard chart is contractible.** -/
theorem contractibleSpace_chartSetAt (i : Fin (d + 1)) :
    ContractibleSpace ↥(chartSetAt (d := d) i) := by
  haveI := contractibleSpace_chartSet d
  exact (chartAtHomeo i).contractibleSpace

/-! ## 3. The charts cover -/

/-- **The standard charts cover `ℂP^d`.**  A point of `ℂP^d` is a projection of trace
`1`, so its diagonal entries cannot all vanish. -/
theorem exists_mem_chartSetAt (z : CP d) : ∃ i : Fin (d + 1), z ∈ chartSetAt i := by
  by_contra hz
  have hall : ∀ i : Fin (d + 1), entry z i i = 0 := by
    intro i
    by_contra hne
    exact hz ⟨i, hne⟩
  have htr : (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace = 0 := by
    show (∑ i, entry z i i) = 0
    exact Finset.sum_eq_zero fun i _ => hall i
  rw [trace_coe] at htr
  exact one_ne_zero htr

/-! ## 4. As open sets -/

/-- The `i`-th standard chart, as an open set of `CPtop d`. -/
def chartOpenAt (i : Fin (d + 1)) : Opens (CPtop d) :=
  ⟨chartSetAt i, isOpen_chartSetAt i⟩

@[simp] theorem mem_chartOpenAt {i : Fin (d + 1)} {z : CP d} :
    z ∈ chartOpenAt i ↔ entry z i i ≠ 0 := Iff.rfl

theorem exists_mem_chartOpenAt (z : CP d) : ∃ i : Fin (d + 1), z ∈ chartOpenAt i :=
  exists_mem_chartSetAt z

end

end CPn
end CharClass
end GroupApproximation
