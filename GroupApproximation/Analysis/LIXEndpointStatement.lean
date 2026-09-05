import GroupApproximation.Analysis.CStarKOneInjectivityCriterion

/-!
# The endpoint shape for STW Problem LIX

STW Problem LIX asks whether every unital simple C-star algebra is `K_1`-injective; the answer
is no.  The endpoint itself is `Manuscript/NinetyNineProblems/ProblemLIX.lean`, which states

    def ProblemLIX : Prop :=
      ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A

and proves `¬ ProblemLIX`, with no named `Prop` hypothesis anywhere in the statement.  This
file is the last generic step before it: the vocabulary `ProblemLIX` is stated over, and the
reduction of the negation to a single unitary.

Two things stand between `Analysis/CStarKOne` and that statement, and both are settled here.

## The order instances

Mathlib's C-star algebra structure on `M_n(A)` (`CStarMatrix.instCStarAlgebra`) asks for
`[PartialOrder A] [StarOrderedRing A]` in addition to `[CStarAlgebra A]`, so `K1Injective` as
defined in `Analysis/CStarKOne` carries those two instance arguments.  They carry no information:
every unital C-star algebra has exactly one order making it a `StarOrderedRing`, namely
`CStarAlgebra.spectralOrder`.  `K1Inj` below is `K1Injective` with that canonical choice
supplied, so it depends on nothing but the C-star structure and can appear under an existential
quantifier that binds only `CStarAlgebra A`.

A downstream file that wants to *discharge* the hypotheses of `not_k1Inj_of_witness` must open
with the same two local instances

    noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
    local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

so that its `diagOne u` is the same term as the one here.  That is the repository's standing
idiom for `CStarMatrix`.

## What remains

`HasK1InjWitness A` names the condition that `A` carries one unitary `u` with

* `u ∉ U_0(A)`, and
* `diag (u, 1) ∈ U_0(M_2(A))`,

and `not_k1Inj_of_hasWitness` reduces `¬ K1Inj A` to it.

Nothing about `K_1(A)` itself is needed — in particular not `K_1(A) = 0`, whose proof would
require Bott periodicity, Morita invariance and continuity of `K`-theory, none of which exist in
Mathlib.  See `Analysis/CStarKOneInjectivityCriterion` for the reduction and
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` (end of §6) for
why the LIX witness satisfies both conditions.
-/

namespace GroupApproximation

universe u

noncomputable section

section Spectral

variable {A : Type u} [inst : CStarAlgebra A]

noncomputable local instance instSpectralPartialOrder (B : Type u) [CStarAlgebra B] :
    PartialOrder B := CStarAlgebra.spectralOrder B

local instance instSpectralStarOrderedRing (B : Type u) [CStarAlgebra B] :
    StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

variable (A) in
/-- `K_1`-injectivity of a unital C-star algebra: the canonical map `U(A)/U_0(A) → K_1(A)` is
injective.  This is `K1Injective` with the canonical spectral order supplied, so that the
predicate depends on nothing but the C-star structure. -/
def K1Inj : Prop := K1Injective A

theorem k1Inj_iff : K1Inj A ↔ Function.Injective (kappa A) := Iff.rfl

/-- **The LIX reduction, in endpoint form.**  A unitary `u` of `A` that is not null-homotopic
in `U(A)` but whose block sum `diag (u, 1)` is null-homotopic in `U(M_2(A))` refutes
`K_1`-injectivity of `A`. -/
theorem not_k1Inj_of_diagOne_mem {u : unitary A} (hu : u ∉ unitaryComponentOne A)
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) : ¬ K1Inj A :=
  not_k1Injective_of_diagOne_mem hu hdiag

/-- The existence form: a single such unitary refutes `K_1`-injectivity. -/
theorem not_k1Inj_of_witness
    (h : ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
      diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) : ¬ K1Inj A :=
  not_k1Injective_of_exists_witness h

variable (A) in
/-- **The witness condition**, as a named proposition: `A` carries a unitary that is not
null-homotopic in `U(A)` but whose block sum `diag (u, 1)` is null-homotopic in `U(M_2(A))`.

This is the whole of what a counterexample to `K_1`-injectivity has to produce, and it is a
named `Prop` rather than an inline existential so that the lane building the algebra can target
it directly.  `diagOne` and `CStarMat 2 A` elaborate only under `[PartialOrder A]` and
`[StarOrderedRing A]`, which the two local instances above fix to the spectral order; the same
existential written out under a differently named pair of local instances is a different term,
definitionally equal but not syntactically so, and joining the two then costs a transport
lemma.  A producer should write `HasK1InjWitness A` and re-register the same two instances

    attribute [local instance] GroupApproximation.instSpectralPartialOrder
                               GroupApproximation.instSpectralStarOrderedRing

rather than declare its own. -/
def HasK1InjWitness : Prop :=
  ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
    diagOne u ∈ unitaryComponentOne (CStarMat 2 A)

theorem hasK1InjWitness_iff :
    HasK1InjWitness A ↔ ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
      diagOne u ∈ unitaryComponentOne (CStarMat 2 A) := Iff.rfl

/-- **The LIX reduction, in the form the endpoint uses.**  An algebra with a witness is not
`K_1`-injective. -/
theorem not_k1Inj_of_hasWitness (h : HasK1InjWitness A) : ¬ K1Inj A :=
  not_k1Inj_of_witness h

/-- The endpoint assembly, with the structural predicate left as an explicit argument.

Substituting a conjunction of simplicity, separability and nontriviality for `P` and the limit
algebra for `A` turns this into the STW LIX endpoint.  `P` ranges over bare types here; a
predicate that needs the C-star structure — as simplicity does — is supplied as
`fun B => ∃ _ : CStarAlgebra B, …`, or else the assembly is written out directly, which is the
one-line `⟨A, inst, hP, not_k1Inj_of_witness h⟩`.

**This is an assembly schema and not an endpoint.**  `P` is a free variable, so the statement
is true for every `P` — it repackages its own hypothesis `hP` — and it says nothing whatever
about simplicity.  The endpoint is `Manuscript/NinetyNineProblems/ProblemLIX.lean`'s
`not_problemLIX`, where `P` is the actual conjunction and every clause is proved.  Recorded
here because a theorem of this shape, in a file with this name, is one citation away from
being read as the endpoint it is not. -/
theorem exists_cstarAlgebra_not_k1Inj {P : Type u → Prop} (hP : P A)
    (h : ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
      diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) :
    ∃ (B : Type u) (_ : CStarAlgebra B), P B ∧ ¬ K1Inj B :=
  ⟨A, inst, hP, not_k1Inj_of_witness h⟩

end Spectral

end

end GroupApproximation
