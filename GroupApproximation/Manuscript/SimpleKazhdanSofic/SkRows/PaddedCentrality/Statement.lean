import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedCentrality.Roots
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Matrix.Diagonal

/-!
# Padded centrality: the target and the column/row action interface

Lane `sk-rows-14` (Khanh, arXiv:2609.08428, Lemma 5.6).

* `PaddedCentralityStatement m R`: the image of `K₂(m, R)` under the stabilization
  `stab : St_m(R) → St_{m+1}(R)` is central in `St_{m+1}(R)`.  Only this *padded* form is
  claimed.  Centrality of `K₂(n, R)` in `St_n(R)` itself is not known over arbitrary
  noncommutative rings and is not stated anywhere here.
* `SteinbergColumnActionStatement m R`: the interface of lane `sk-rows-13`, which is not on
  disk.  For `y ∈ St_m(R)` with matrix `M = projection y`, conjugation by `stab y` acts on the
  last-column roots through `M` and on the last-row roots through `M⁻¹`:

  `stab y · x_{i,m+1}(a) · (stab y)⁻¹ = ∏_k x_{k,m+1}(M_{k i} a)`,
  `stab y · x_{m+1,i}(a) · (stab y)⁻¹ = ∏_k x_{m+1,k}(a (M⁻¹)_{i k})`.

  The products are `List.prod` over `List.finRange m`, because `St_{m+1}(R)` is not
  commutative.  The factors of each product commute pairwise, so the order does not matter.

## Truth check of the interface

Over any ring and for every `m`, the set of `y` satisfying both formulas contains `1`.  It is
closed under products because `M(y₁ y₂) = M(y₁) M(y₂)` and the column (row) roots form an
abelian group isomorphic to `R^m`.  It is closed under inverses by the same argument, and it
contains each generator `x_{pq}(c)`.  For the generator case, conjugation by `x_{pq}(c)` fixes
`x_{k,m+1}(b)` for `k ≠ q`.  It sends `x_{q,m+1}(b)` to `x_{p,m+1}(c b) · x_{q,m+1}(b)`, since
`⁅x_{pq}(c), x_{q,m+1}(b)⁆ = x_{p,m+1}(c b)`.  This is the column of `E_{pq}(c) = 1 + c e_{pq}`.
It sends `x_{m+1,p}(b)` to `x_{m+1,p}(b) · x_{m+1,q}(-b c)`, which is the row of
`E_{pq}(c)⁻¹ = 1 - c e_{pq}`.  So the interface is true.  Its proof is lane 13's content.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality

open GroupApproximation.BooneHigman.SteinbergBasic

variable (m : ℕ) (R : Type*) [Ring R]

/-- The matrix `projection y ∈ E_m(R) ≤ GL_m(R)` of a Steinberg element `y ∈ St_m(R)`. -/
def projectionMatrix (y : St m R) : Matrix (Fin m) (Fin m) R :=
  ((SteinbergGroup.projection y : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.projectionMatrix

/-- **Target of lane `sk-rows-14`** (Khanh's padded centrality).  The image of `K₂(m, R)` under the
stabilization `St_m(R) → St_{m+1}(R)` is central. -/
def PaddedCentralityStatement : Prop :=
  (K2n m R).map (stab m R) ≤ Subgroup.center (St (m + 1) R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.PaddedCentralityStatement

/-- **Interface of lane `sk-rows-13`** (not on disk).  The stabilized Steinberg group acts on the
last-column roots through the projection matrix and on the last-row roots through its inverse. -/
def SteinbergColumnActionStatement : Prop :=
  ∀ (y : St m R) (i : Fin m) (a : R),
    stab m R y * colRoot m R i a * (stab m R y)⁻¹ =
        ((List.finRange m).map fun k ↦ colRoot m R k (projectionMatrix m R y k i * a)).prod ∧
      stab m R y * rowRoot m R i a * (stab m R y)⁻¹ =
        ((List.finRange m).map fun k ↦ rowRoot m R k (a * projectionMatrix m R y⁻¹ i k)).prod

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.SteinbergColumnActionStatement

variable {m R}

/-- A list product in which every factor except the one at `i` is `1`. -/
theorem list_prod_map_eq_of_eq_one {G ι : Type*} [Monoid G] {l : List ι} (hl : l.Nodup)
    {i : ι} (hi : i ∈ l) {f : ι → G} (hf : ∀ k, k ≠ i → f k = 1) :
    (l.map f).prod = f i := by
  induction l with
  | nil => exact absurd hi List.not_mem_nil
  | cons j t ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons]
    by_cases hji : j = i
    · rw [hji] at hl
      rw [hji, List.prod_eq_one, mul_one]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      exact hf k fun hki ↦ hl.1 (hki ▸ hk)
    · have hit : i ∈ t := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hji
        · exact h
      rw [hf j hji, one_mul]
      exact ih hl.2 hit

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.list_prod_map_eq_of_eq_one

/-- The column formula at the identity matrix collapses to a single root. -/
theorem prod_colRoot_one (i : Fin m) (a : R) :
    ((List.finRange m).map fun k ↦
        colRoot m R k ((1 : Matrix (Fin m) (Fin m) R) k i * a)).prod = colRoot m R i a := by
  rw [list_prod_map_eq_of_eq_one (List.nodup_finRange m) (List.mem_finRange i)]
  · simp
  · intro k hk
    simp [Matrix.one_apply_ne hk]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.prod_colRoot_one

/-- The row formula at the identity matrix collapses to a single root. -/
theorem prod_rowRoot_one (i : Fin m) (a : R) :
    ((List.finRange m).map fun k ↦
        rowRoot m R k (a * (1 : Matrix (Fin m) (Fin m) R) i k)).prod = rowRoot m R i a := by
  rw [list_prod_map_eq_of_eq_one (List.nodup_finRange m) (List.mem_finRange i)]
  · simp
  · intro k hk
    simp [Matrix.one_apply_ne hk.symm]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.prod_rowRoot_one

/-- An element of `K₂(m, R)` has identity projection matrix. -/
theorem projectionMatrix_eq_one_of_mem_K2 {y : St m R} (hy : y ∈ K2n m R) :
    projectionMatrix m R y = 1 := by
  have h := congrArg
    (fun g : elementaryGroup (Fin m) R ↦ ((g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R))
    ((mem_K2_iff y).mp hy)
  simpa [projectionMatrix] using h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.projectionMatrix_eq_one_of_mem_K2

end GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
