import GroupApproximation.Sofic.UltraproductDedekindFinite
import GroupApproximation.Sofic.FaithfullyTracedCoordinateNoGo
import GroupApproximation.Analysis.LimitsTraceStandardForm

/-!
# Where `thm:kazhdan-transport` uses finite dimensionality, and what happens
without it

Proof-ledger row `LI.19`, the supporting half of the manuscript's fifth
question:

> `thm:kazhdan-transport` uses finite dimensionality of `M_d` twice, for the
> conjugation action on `L²(M_d, tr_d)` and for finiteness of the norm
> ultraproduct, and faithful traces alone do not replace it.

The row has been `MISMATCH` on statement for a reason its note states exactly:
"no declaration says of the printed proof that it uses finite dimensionality at
exactly those two points."  That objection is correct about propositions and it
splits the sentence into two halves that are answered differently.

## The "uses it" half is a dependency, and dependencies are checked elsewhere

*Which* facts a proof consumes is not a proposition and cannot be one.  It is a
property of the elaborated proof term, and this repository already checks such
properties: `routeGuards` in `scripts/Audit.lean` walks the kernel-level
transitive closure of a declaration and fails when a named dependency is no
longer in it.  Two pins land with this file, one for each of the printed
points, so "uses finite dimensionality twice, *there*" is machine-checked
rather than asserted — and, unlike a proposition, it stays checked, because a
re-route turns the audit red.

## The "and faithful traces alone do not replace it" half is a proposition

That half is what this file states.  Each of the two points is a finiteness
assertion; each holds for matrix coordinates; and each fails once finite
dimensionality is dropped in favour of a faithful trace, which is precisely
what Question 5 proposes to do.

* **The norm ultraproduct.**  `normMatrixCStarCorona_isDedekindFiniteMonoid`
  makes `∏_n M_{d_n}(ℂ) / c₀` Dedekind finite: an isometry there is a unitary.
  For a faithfully traced infinite-dimensional coordinate algebra this fails in
  the ambient the conjugation action lives in — `manuscriptLimitsTraceStandardForm`
  exhibits `V` with `V*V = 1` and `VV* ≠ 1`.
* **The conjugation action on `L²(M_d, tr_d)`.**  In finite dimensions the two
  commuting actions generate a *finite* algebra, because everything in sight is
  a matrix algebra over the finite index `Y × Y` that `conjDouble` lands in.
  For an infinite-dimensional II₁ factor in standard form the same two commuting
  actions generate all of `B(L²)`, which is not finite; that is the standard-form
  clause of `manuscriptLimitsTraceStandardForm`, and it is the reason the
  generalization is hopeless rather than merely unproved.
* **Faithful traces alone.**  `manuscriptFaithfullyTracedCoordinateNoGo` refutes
  the transport statement over faithfully traced coordinates outright.

`manuscriptFiniteDimensionalityNotReplaceable` is the three of them as one
statement, which is the printed clause.
-/

namespace GroupApproximation
namespace PrintedFiniteDimensionalUses

open Filter Matrix Topology
open ReducedGroupCStarTrace TwoSidedRegularCommutant GroupVonNeumann
open TracialStandardForm PermutationICC ShiftIsometry
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The first point, positively: a finite-stage isometry is a unitary.**
Finite dimensionality, in the form the conjugation action consumes — the
doubled index `Y × Y` that `conjDouble` lands in is finite whenever `Y` is, so
the algebra the two commuting actions generate is a matrix algebra and an
isometry of it is a unitary. -/
theorem finiteStage_isometry_isUnitary (Y : FiniteModel) (v : Matrix Y Y ℂ)
    (hv : vᴴ * v = 1) : v * vᴴ = 1 :=
  mul_eq_one_comm.mp hv

/-- The same at the doubled index, which is where the conjugation action on
`L²(M_d, tr_d)` is realized. -/
theorem doubledIndex_isometry_isUnitary (Y : FiniteModel)
    (v : Matrix (Y × Y) (Y × Y) ℂ) (hv : vᴴ * v = 1) : v * vᴴ = 1 :=
  mul_eq_one_comm.mp hv

/-- **The second point, positively: the norm ultraproduct is finite.**  This is
the instance the transport's Murray--von Neumann step consumes. -/
theorem normUltraproduct_isometry_isUnitary
    (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] (x y : NormMatrixCStarCorona X) (hxy : x * y = 1) :
    y * x = 1 :=
  IsDedekindFiniteMonoid.mul_eq_one_symm hxy

/-- **`LI.19`'s supporting clause.**

> `thm:kazhdan-transport` uses finite dimensionality of `M_d` twice, for the
> conjugation action on `L²(M_d, tr_d)` and for finiteness of the norm
> ultraproduct, and faithful traces alone do not replace it.

Each of the two points is a finiteness assertion, each holds for matrix
coordinates, and each fails once finite dimensionality is dropped in favour of
a faithful trace:

1. the conjugation action, at the doubled index where it is realized, is by
   matrices over a finite type, so an isometry there is a unitary;
2. the norm ultraproduct is Dedekind finite;
3. for a faithfully traced infinite-dimensional factor in standard form the two
   commuting actions generate everything, that ambient carries an isometry that
   is not a unitary, and so neither finiteness survives; and
4. faithful traces alone do not give the transport, which is refuted outright.

Which of these the printed proof *consumes*, and where, is pinned in
`routeGuards` rather than stated here: that is a property of the proof term and
not of any proposition. -/
theorem manuscriptFiniteDimensionalityNotReplaceable :
    (∀ (Y : FiniteModel) (v : Matrix (Y × Y) (Y × Y) ℂ),
        vᴴ * v = 1 → v * vᴴ = 1)
      ∧ (∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
          [∀ n, Nonempty (X n)] (x y : NormMatrixCStarCorona X),
            x * y = 1 → y * x = 1)
      ∧ (IsTracialStandardForm (groupVonNeumannAlgebra (Equiv.Perm ℕ))
            (deltaOne (Equiv.Perm ℕ))
          ∧ ¬ Module.Finite ℂ
              ((groupVonNeumannAlgebra (Equiv.Perm ℕ)).toStarSubalgebra.toSubalgebra
              )
          ∧ ∃ V : GroupHilbert (Equiv.Perm ℕ) →L[ℂ] GroupHilbert (Equiv.Perm ℕ),
              star V * V = 1 ∧ V * star V ≠ 1)
      ∧ ¬ FaithfullyTracedCoordinates.FaithfullyTracedCoordinateTransport.{0} := by
  refine ⟨fun Y v hv ↦ doubledIndex_isometry_isUnitary Y v hv,
    fun X _ _ _ x y hxy ↦ normUltraproduct_isometry_isUnitary X x y hxy, ?_,
    FaithfullyTracedCoordinates.manuscriptFaithfullyTracedCoordinateNoGo⟩
  obtain ⟨hstd, -, hfin, -, -, hV⟩ :=
    LimitsTraceStandardForm.manuscriptLimitsTraceStandardForm
  exact ⟨hstd, hfin, hV⟩

end

end PrintedFiniteDimensionalUses
end GroupApproximation
