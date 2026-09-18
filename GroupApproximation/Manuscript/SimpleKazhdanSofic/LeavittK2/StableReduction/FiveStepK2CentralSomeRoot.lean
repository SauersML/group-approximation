import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepK2CentralConj
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralLeavitt
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner-root centrality from one nonzero coefficient per element (lane sk-leavitt-37, endpoint)

Write `L = L_{𝔽₂}(1,2)`.  The target `FiveStepCentralLeavittCornerStatement`
(`FiveStepCentralLeavitt.lean`) says every `k ∈ K₂(5, L)` commutes with `x_{01}(s₀ t₀)`.
This module reduces it to

  `FiveStepK2CentralSomeRootStatement`: for every `k ∈ K₂(5, L)` there are a root `(i, j)` and a
  coefficient `a ≠ 0`, both allowed to depend on `k`, such that `x_{ij}(a)` commutes with every
  conjugate `g k g⁻¹`, `g ∈ St_5(L)`

(`fiveStepK2Central_fiveStepCentralLeavittCorner_of_someRoot`).  The passage uses only that `L` is
sandwich divisible (`u a v = 1` for `a ≠ 0`, `BinaryLeavitt.hasSingleSandwichDivision`); see
`fiveStepK2Central_mem_center_of_conj_commute` (`FiveStepK2CentralConj.lean`), proved over any
such ring and for `k` not assumed in `K₂`.

## LOUD: logically equivalent, smaller in proof content only

The converse is proved (`fiveStepK2CentralSomeRoot_of_fiveStepCentralLeavittCorner`), so the new
statement is **logically equivalent** to the target.  No sufficient condition implied by a true
target can be strictly weaker.  The gain is in what must be exhibited.  The target fixes the root
`(0, 1)` and the coefficient `s₀ t₀` uniformly for all of `K₂(5, L)`.  The new statement lets
both depend on `k`, with any nonzero coefficient.  In exchange it asks commutation with all
conjugates of `k`; for `K₂` this costs nothing, since `K₂` is normal.

## Negative finding: the lane's premise is not a theorem

The brief calls "`K₂(n, R)` is central in `St_n(R)` for `n ≥ 5`, any ring `R`" a standard fact.
It is **not**.  Milnor's argument (Milnor, *Introduction to algebraic K-theory*, §5) proves only
*stable* centrality, i.e. `stab K₂(n) ≤ Z(St_{n+1})`, over any ring.  That is proved in the corpus
(`map_stab_K2_le_center`, `PaddedCentral.lean`).  The argument uses a spare index `n+1` that does
not occur in `k`: the column group `P_{n+1}` is abelian and `k` acts on it through its matrix.  A
general `k ∈ K₂(5)` has no spare index.  Unstable centrality is known for commutative rings (van
der Kallen) and for quasi-finite rings with `n ≥ 5` (Tulenbaev).  `L` is neither: it is simple,
finitely generated and infinite-dimensional over its centre `𝔽₂`.  So no Steinberg-relations-only
proof of the target is available.

Two Leavitt substitutes for the spare index fail.
* *The corner half `p₁ = s₁ t₁` of an index.*  The corner endomorphism `σ_r` of
  `FiveStepCorner.lean` frees the half `p₁` of index `r`.  But the spare root elements
  `x_{ir}(c)`, `c = c p₁`, are opposite to the generators `x_{ri}(s₀ b)` of the image of `σ_r`.
  Opposite roots have no Steinberg relation.
* *The doubling endomorphism `θ(a) = s₀ a t₀ + s₁ a t₁`.*  On generators `St(θ) = ψ₀ · ψ₁`, and the
  image of `ψ₁` commutes with `x_{01}(p₀)` (`FiveStepCentralLeavittLower.lean`).  But the `ψ₀`
  factor returns the target for `ψ₀(k)`, which needs injectivity of `ψ₀` on commutators.

## Truth check

`K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4) gives the target and the new statement
(`fiveStepK2CentralSomeRoot_of_binaryLeavittSteinbergInjective`).  Not proved in Lean.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- **One nonzero root coefficient per element of `K₂(5, L)`**, for `L = L_{𝔽₂}(1,2)`: for every
`k ∈ K₂(5, L)` some `x_{ij}(a)` with `a ≠ 0` commutes with every conjugate of `k`.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`fiveStepK2CentralSomeRoot_of_binaryLeavittSteinbergInjective`.  Not proved in Lean.
*Why it is smaller.*  The root and the coefficient may depend on `k`, and any `a ≠ 0` will do.
LOUD: it is logically equivalent to `FiveStepCentralLeavittCornerStatement` (see
`fiveStepK2CentralSomeRoot_of_fiveStepCentralLeavittCorner`). -/
def FiveStepK2CentralSomeRootStatement : Prop :=
  ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    ∃ (i j : Fin 5) (hij : i ≠ j) (a : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)), a ≠ 0 ∧
      ∀ g : SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
        Commute (g * k * g⁻¹) (x i j hij a)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FiveStepK2CentralSomeRootStatement

/-- The new statement gives centrality of `K₂(5, L)`. -/
theorem fiveStepK2Central_binaryLeavittK2FiveCentral_of_someRoot
    (h : FiveStepK2CentralSomeRootStatement) : BinaryLeavittK2FiveCentralStatement := by
  unfold BinaryLeavittK2FiveCentralStatement
  exact fiveStepK2Central_K2_le_center_of_someRoot
    (GroupApproximation.BinaryLeavitt.hasSingleSandwichDivision (ZMod 2)) (n := 5) (by omega) h

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2Central_binaryLeavittK2FiveCentral_of_someRoot

/-- **Endpoint.**  The new statement gives corner-root centrality. -/
theorem fiveStepK2Central_fiveStepCentralLeavittCorner_of_someRoot
    (h : FiveStepK2CentralSomeRootStatement) : FiveStepCentralLeavittCornerStatement :=
  fiveStepCentralLeavittCorner_of_binaryLeavittK2FiveCentral
    (fiveStepK2Central_binaryLeavittK2FiveCentral_of_someRoot h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2Central_fiveStepCentralLeavittCorner_of_someRoot

/-- The new statement also gives single-root centrality. -/
theorem fiveStepK2Central_fiveStepCentralRoot_of_someRoot
    (h : FiveStepK2CentralSomeRootStatement) : FiveStepCentralRootStatement :=
  fiveStepCentralRoot_of_fiveStepCentralLeavittCorner
    (fiveStepK2Central_fiveStepCentralLeavittCorner_of_someRoot h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2Central_fiveStepCentralRoot_of_someRoot

/-- The converse (LOUD: equivalence).  Centrality gives the new statement, with the root `(0, 1)`
and the coefficient `1`. -/
theorem fiveStepK2CentralSomeRoot_of_binaryLeavittK2FiveCentral
    (h : BinaryLeavittK2FiveCentralStatement) : FiveStepK2CentralSomeRootStatement := by
  unfold FiveStepK2CentralSomeRootStatement
  intro k hk
  refine ⟨0, 1, fiveStepCentral_zero_ne_one, 1, one_ne_zero, fun g => ?_⟩
  have hc : g * k * g⁻¹ ∈
      Subgroup.center (SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    h ((BooneHigman.SteinbergBasic.K2_normal (Fin 5)
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).conj_mem k hk g)
  exact (Subgroup.mem_center_iff.mp hc _).symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralSomeRoot_of_binaryLeavittK2FiveCentral

/-- The converse from corner-root centrality (LOUD: equivalence). -/
theorem fiveStepK2CentralSomeRoot_of_fiveStepCentralLeavittCorner
    (h : FiveStepCentralLeavittCornerStatement) : FiveStepK2CentralSomeRootStatement :=
  fiveStepK2CentralSomeRoot_of_binaryLeavittK2FiveCentral
    (fiveStepCentralLeavitt_binaryLeavittK2FiveCentral_of_corner h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralSomeRoot_of_fiveStepCentralLeavittCorner

/-- **Truth check.**  `K₂(5, L) = ⊥` gives the new statement. -/
theorem fiveStepK2CentralSomeRoot_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    FiveStepK2CentralSomeRootStatement :=
  fiveStepK2CentralSomeRoot_of_binaryLeavittK2FiveCentral
    (binaryLeavittK2FiveCentral_of_binaryLeavittSteinbergInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralSomeRoot_of_binaryLeavittSteinbergInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
