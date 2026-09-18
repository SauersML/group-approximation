import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCorner
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStabilityStep
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Endpoints
import GroupApproximation.Algebra.ElementaryPaddingInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# The step `K₂(5) → K₂(6)` splits into centrality and corner injectivity (sk-leavitt-32)

Write `L = L_{𝔽₂}(1,2)`, `σ = σ_{last 4}` for the corner endomorphism of `St_5(L)`
(`FiveStepCorner.lean`), and `D = refineHom L (last 4) : St_5(L) → St_6(L)`.

## LOUD: this is a split, NOT a strictly weaker statement

`BinaryLeavittK2FiveStepStatement` is proved **equivalent** to the conjunction of
* `BinaryLeavittK2FiveCentralStatement`: `K₂(5, L)` is central in `St_5(L)`;
* `BinaryLeavittFiveCornerInjectiveStatement`: `σ` is injective on `St_5(L)`.

Each conjunct is implied by the step (proved here), and so is strictly weaker *as a single
statement*.  Their conjunction is only equivalent to the step.  Neither conjunct is proved.
Both are true, because `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see the `_of_`
truth-check endpoints.

What the split buys, unconditionally:
* `D ∘ σ = pad_{5 → 6}` (`fiveStep_refineHom_comp_cornerHom`).
* `ker σ ≤ K₂(5)` (`fiveStep_projection_eq_one_of_cornerHom_eq_one`).
* If `K₂(5)` is central, `D` is injective (sk-leavitt-28), so `ker pad_{5→6} = ker σ`.  The rank
  change is then gone: the step is a question about a *same-rank* endomorphism of `St_5(L)`.

## Negative findings (not formalized)

* **Centrality alone is not formally enough.**  What is left is `H₂(E₅) → H₂(E₆)` injectivity,
  which is homological stability.
* **A normal generating set of `K₂(5)` does not help.**  Injectivity of a homomorphism cannot be
  checked on generators of a normal subgroup.
* **Every retraction `St_6 → St_5` fails already for `N = 6`, at the level of `E`.**  The
  elements `diag(I₅, u)` centralize `pad(E₅)`, so they must go to `Z(GL₅(L)) = 1`.  Their normal
  closure is everything.
* **`σ` has no left inverse.**  At the level of `E`, a hand computation gives `σ² = Ad(U) ∘ σ`
  for a unit `U` built from a partial isomorphism of idempotents of `L`.  On a central `K₂` this
  would make `σ_*` idempotent, so corner injectivity on `K₂(5)` would be equivalent to `σ = id`
  on `K₂(5)`.  None of this is formalized.
* `EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement` implies the step through
  proved machinery, but it is equivalent to the global gap.  It is stronger, not weaker.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R)

/-- **The kernel of the corner endomorphism lies in `K₂`.**  If `σ_r w = 1`, then
`pad w = D_r (σ_r w) = 1`, and padding of elementary groups is injective. -/
theorem fiveStep_projection_eq_one_of_cornerHom_eq_one {n : ℕ} (r : Fin n)
    {w : SteinbergGroup (Fin n) R} (hw : fiveStepCornerHom L r w = 1) : projection w = 1 := by
  have h1 : indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n)) w = 1 := by
    rw [← fiveStep_refineHom_cornerHom L r w, hw, map_one]
  have h2 : ElementaryPadding.elementaryPad (R := R) (Fin.castLEEmb (Nat.le_succ n))
      (projection w) = 1 := by
    rw [← Full.LVH2GL3.projection_indexMap, h1, map_one]
  exact ElementaryPadding.elementaryPad_injective (Fin.castLEEmb (Nat.le_succ n))
    (by rw [h2, map_one])

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStep_projection_eq_one_of_cornerHom_eq_one

/-- **Under centrality, a death one rank up is a death under the corner endomorphism.**  `D_r` is
injective when `K₂(n)` is central, and `D_r (σ_r w) = pad w`. -/
theorem fiveStep_cornerHom_eq_one_of_indexMap_eq_one {n : ℕ} (hn : 4 ≤ n) (r k : Fin n)
    (hk : k ≠ r)
    (hC : BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R))
    {w : SteinbergGroup (Fin n) R}
    (hw : indexMap (R := R) (Fin.castLEEmb (Nat.le_succ n)) w = 1) :
    fiveStepCornerHom L r w = 1 :=
  fiveStability_eq_one_of_refineHom_eq_one L hn r k hk hC
    ((fiveStep_refineHom_cornerHom L r w).trans hw)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStep_cornerHom_eq_one_of_indexMap_eq_one

/-- **One-step injective stability from centrality and corner injectivity.** -/
theorem fiveStep_k2StabInjective_of_central_of_cornerInjective {n : ℕ} (hn : 4 ≤ n)
    (r k : Fin n) (hk : k ≠ r)
    (hC : BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R))
    (hσ : ∀ w : SteinbergGroup (Fin n) R, fiveStepCornerHom L r w = 1 → w = 1) :
    Full.LVH2GL3.K2StabInjective R n := by
  intro w _ hw
  exact hσ w (fiveStep_cornerHom_eq_one_of_indexMap_eq_one L hn r k hk hC hw)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStep_k2StabInjective_of_central_of_cornerInjective

/-- **Corner injectivity from one-step injective stability.**  A `w` with `σ_r w = 1` lies in `K₂`
and dies under padding, since `pad w = D_r (σ_r w)`. -/
theorem fiveStep_cornerInjective_of_k2StabInjective {n : ℕ} (r : Fin n)
    (hS : Full.LVH2GL3.K2StabInjective R n) :
    ∀ w : SteinbergGroup (Fin n) R, fiveStepCornerHom L r w = 1 → w = 1 := by
  intro w hw
  refine hS w (fiveStep_projection_eq_one_of_cornerHom_eq_one L r hw) ?_
  rw [← fiveStep_refineHom_cornerHom L r w, hw, map_one]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStep_cornerInjective_of_k2StabInjective

/-! ### The binary Leavitt algebra `L_{𝔽₂}(1,2)` at rank five -/

/-- **Centrality of `K₂(5, L)`** in `St_5(L)`, for `L = L_{𝔽₂}(1,2)`.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective`.  Not proved in Lean.  It is
implied by the step (`binaryLeavittK2FiveCentral_of_fiveStep`). -/
def BinaryLeavittK2FiveCentralStatement : Prop :=
  BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
    Subgroup.center (SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittK2FiveCentralStatement

/-- **Injectivity of the corner endomorphism** `σ_{last 4}` of `St_5(L)`, for
`L = L_{𝔽₂}(1,2)`.

*Why it is true.*  `ker σ ≤ K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`binaryLeavittFiveCornerInjective_of_binaryLeavittSteinbergInjective`.  Not proved in Lean.  It
is implied by the step (`binaryLeavittFiveCornerInjective_of_fiveStep`). -/
def BinaryLeavittFiveCornerInjectiveStatement : Prop :=
  ∀ w : SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    fiveStepCornerHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4) w = 1 → w = 1

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittFiveCornerInjectiveStatement

/-- **The step from centrality and corner injectivity.**  LOUD: the converse is also proved
(`binaryLeavittK2FiveCentral_of_fiveStep`, `binaryLeavittFiveCornerInjective_of_fiveStep`), so
the conjunction is equivalent to the step. -/
theorem binaryLeavittK2FiveStep_of_central_of_cornerInjective
    (hC : BinaryLeavittK2FiveCentralStatement) (hσ : BinaryLeavittFiveCornerInjectiveStatement) :
    BinaryLeavittK2FiveStepStatement :=
  fiveStep_k2StabInjective_of_central_of_cornerInjective (BinaryLeavitt.family (ZMod 2))
    (by omega) (Fin.last 4) ⟨0, by omega⟩
    (fun e => by
      have h1 : (0 : ℕ) = 4 := congrArg Fin.val e
      omega) hC hσ

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStep_of_central_of_cornerInjective

/-- The step gives centrality of `K₂(5, L)`. -/
theorem binaryLeavittK2FiveCentral_of_fiveStep (hS : BinaryLeavittK2FiveStepStatement) :
    BinaryLeavittK2FiveCentralStatement :=
  fiveStability_K2_le_center_of_k2StabInjective hS

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveCentral_of_fiveStep

/-- The step gives injectivity of the corner endomorphism. -/
theorem binaryLeavittFiveCornerInjective_of_fiveStep (hS : BinaryLeavittK2FiveStepStatement) :
    BinaryLeavittFiveCornerInjectiveStatement :=
  fiveStep_cornerInjective_of_k2StabInjective (BinaryLeavitt.family (ZMod 2)) (Fin.last 4) hS

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittFiveCornerInjective_of_fiveStep

/-- **Truth check** for centrality: `K₂(5, L) = ⊥` gives it. -/
theorem binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    BinaryLeavittK2FiveCentralStatement :=
  binaryLeavittK2FiveCentral_of_fiveStep
    (binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective

/-- **Truth check** for corner injectivity: `K₂(5, L) = ⊥` gives it. -/
theorem binaryLeavittFiveCornerInjective_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    BinaryLeavittFiveCornerInjectiveStatement :=
  binaryLeavittFiveCornerInjective_of_fiveStep
    (binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittFiveCornerInjective_of_binaryLeavittSteinbergInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
