import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralLeavittLower
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralBinary
import GroupApproximation.Meta.AxiomGuard

/-!
# Single-root centrality reduces to the corner root `x_{01}(s₀t₀)` (lane sk-leavitt-35, endpoint)

Write `L = L_{𝔽₂}(1,2)`, `p₀ = s₀ t₀` and `p₁ = s₁ t₁`, so that `p₀ + p₁ = 1`.  The target
`FiveStepCentralRootStatement` (`FiveStepCentralBinary.lean`) says every `k ∈ K₂(5, L)` commutes
with `x_{01}(1)`.  This module reduces it to

  `FiveStepCentralLeavittCornerStatement`: every `k ∈ K₂(5, L)` commutes with `x_{01}(p₀)`

(`fiveStepCentralRoot_of_fiveStepCentralLeavittCorner`).  The argument: the centralizer of
`K₂(5, L)` is normal, and a normal subgroup containing `x_{01}(p₀)` contains `x_{01}(1)`.  The
second fact is `fiveStepCentralLeavitt_mem_of_corner_mem` (`FiveStepCentralLeavittSpread.lean`),
through the Leavitt identity `p₁ = (s₁ t₀) p₀ (s₀ t₁)` and `x_{01}(1) = x_{01}(p₀) x_{01}(p₁)`.

## LOUD: logically equivalent, smaller in proof content only

The converse is also proved (`fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral`), so the
new statement is **logically equivalent** to the target.  It is **not** strictly weaker.  The gain
is in proof content.
* The `p₁` half of `x_{01}(1) = x_{01}(p₀) x_{01}(p₁)` is gone.
* The part of `St_5(L)` in the image of the lower corner `ψ₁ : x_{ij}(a) ↦ x_{ij}(s₁ a t₁)` is
  settled unconditionally (`fiveStepCentralLeavittCorner_commute_of_mem_range`).  The whole image
  of `ψ₁` commutes with `x_{01}(p₀)`, not only its intersection with `K₂(5, L)`
  (`fiveStepCentralLeavitt_commute_lowerHom`, `FiveStepCentralLeavittLower.lean`).

## Remaining gap

To commute a general `k ∈ K₂(5, L)` with `x_{01}(p₀)`.  This is open here when `k` is outside
the image of `ψ₁`.

## Truth check

`K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4) gives the target, and hence the new statement
(`fiveStepCentralLeavittCorner_of_binaryLeavittSteinbergInjective`).  So both are true.

## Negative findings

* Unstable centrality of `K₂(n, R)` for noncommutative `R` that is not quasi-finite is open as far
  as this lane knows (see `FiveStepCentralBinary.lean`).
* Choosing a spare index by merging or halving indices via the Leavitt structure does not work.
  The conjugating elements need the diagonal entries of `k`, and those are not controlled.
* The refinement `D : St_4 → St_5` is surjective (`LeavittFP.refineHom_surjective`).  Without
  injectivity this does not move `K₂(5)` into the image of padding.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- **Corner-root centrality of `K₂(5, L)`**, for `L = L_{𝔽₂}(1,2)`: every element of `K₂(5, L)`
commutes with `x_{01}(s₀ t₀)` in `St_5(L)`.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`fiveStepCentralLeavittCorner_of_binaryLeavittSteinbergInjective`.  Not proved in Lean.
*Why it is smaller.*  The coefficient `1 = p₀ + p₁` becomes the corner idempotent `p₀`.  The
image of the lower corner `ψ₁` is handled unconditionally.  LOUD: it is logically equivalent to
`FiveStepCentralRootStatement` (see `fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral`). -/
def FiveStepCentralLeavittCornerStatement : Prop :=
  ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    Commute k (x (0 : Fin 5) 1 fiveStepCentral_zero_ne_one
      ((BinaryLeavitt.family (ZMod 2)).s0 * (BinaryLeavitt.family (ZMod 2)).t0))

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FiveStepCentralLeavittCornerStatement

/-- **Endpoint.**  Corner-root centrality gives single-root centrality. -/
theorem fiveStepCentralRoot_of_fiveStepCentralLeavittCorner
    (h : FiveStepCentralLeavittCornerStatement) : FiveStepCentralRootStatement := by
  unfold FiveStepCentralRootStatement
  intro k hk
  have hx0 : x (0 : Fin 5) 1 fiveStepCentral_zero_ne_one
      ((BinaryLeavitt.family (ZMod 2)).s0 * (BinaryLeavitt.family (ZMod 2)).t0) ∈
      Subgroup.centralizer
        (BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :
          Set (SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))) :=
    Subgroup.mem_centralizer_iff.mpr fun k' hk' => (h k' hk').eq
  have hx := fiveStepCentralLeavitt_mem_of_corner_mem (BinaryLeavitt.family (ZMod 2)) (n := 5)
    (by omega)
    (Subgroup.centralizer
      (BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :
        Set (SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))))
    fiveStepCentral_zero_ne_one hx0
  exact Subgroup.mem_centralizer_iff.mp hx k hk

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralRoot_of_fiveStepCentralLeavittCorner

/-- **Composite endpoint.**  Corner-root centrality gives centrality of `K₂(5, L)`. -/
theorem fiveStepCentralLeavitt_binaryLeavittK2FiveCentral_of_corner
    (h : FiveStepCentralLeavittCornerStatement) : BinaryLeavittK2FiveCentralStatement :=
  binaryLeavittK2FiveCentral_of_fiveStepCentralRoot
    (fiveStepCentralRoot_of_fiveStepCentralLeavittCorner h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_binaryLeavittK2FiveCentral_of_corner

/-- The converse (LOUD: equivalence).  Centrality gives corner-root centrality. -/
theorem fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral
    (h : BinaryLeavittK2FiveCentralStatement) : FiveStepCentralLeavittCornerStatement := by
  unfold FiveStepCentralLeavittCornerStatement
  intro k hk
  exact (Subgroup.mem_center_iff.mp (h hk) _).symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral

/-- The converse from single-root centrality (LOUD: equivalence). -/
theorem fiveStepCentralLeavittCorner_of_fiveStepCentralRoot
    (h : FiveStepCentralRootStatement) : FiveStepCentralLeavittCornerStatement :=
  fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral
    (binaryLeavittK2FiveCentral_of_fiveStepCentralRoot h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavittCorner_of_fiveStepCentralRoot

/-- **Truth check.**  `K₂(5, L) = ⊥` gives corner-root centrality. -/
theorem fiveStepCentralLeavittCorner_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    FiveStepCentralLeavittCornerStatement :=
  fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral
    (binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavittCorner_of_binaryLeavittSteinbergInjective

/-- **Unconditional part.**  Every element of the image of the lower corner
`ψ₁ : St_5(L) → St_5(L)` commutes with `x_{01}(s₀ t₀)`.  In particular this holds for every
element of `K₂(5, L)` in that image. -/
theorem fiveStepCentralLeavittCorner_commute_of_mem_range
    (k : SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
    (hk : k ∈ (fiveStepCentralLeavittLowerHom (BinaryLeavitt.family (ZMod 2)) (n := 5)).range) :
    Commute k (x (0 : Fin 5) 1 fiveStepCentral_zero_ne_one
      ((BinaryLeavitt.family (ZMod 2)).s0 * (BinaryLeavitt.family (ZMod 2)).t0)) := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hk
  exact (fiveStepCentralLeavitt_commute_lowerHom (BinaryLeavitt.family (ZMod 2)) (n := 5)
    (by omega) fiveStepCentral_zero_ne_one g).symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavittCorner_commute_of_mem_range

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
