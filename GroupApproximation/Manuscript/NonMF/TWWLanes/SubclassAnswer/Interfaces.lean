import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.FaithfulTracialState
import GroupApproximation.Analysis.KKTheoryKasparov
import GroupApproximation.Meta.AxiomGuard

/-!
# TWW lanes, subclass answer: vocabulary and upstream interfaces

Lane `nm-tww-05` (cartography `lanes/carto-nm-tww.md`). It concerns census row
`82cac0c03a39`, `non_mf_groups_exist.tex` L315--318:

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

**This lane proves an answer on a SUBCLASS only**: separable algebras that are
commutative or AF. It does not formalize the printed sentence, which quantifies
over the whole UCT/faithful-trace class. That class needs the full TWW theorem
at Kasparov's `KK` (see `RelatedTWW/KasparovDegenerate.lean`: at a degenerate
Kasparov theory the TWW statement is the open UCT-free problem).

## What this module fixes

* `Multimatrix r k`, the multimatrix algebra `⊕_{i<r} M_{k_i}(ℂ)`.
* `MultimatrixAFPresentation A`, an explicit unital AF presentation of `A`: an
  increasing sequence of injective unital ⋆-homomorphisms from multimatrix
  algebras into `A` whose ranges have dense union. This is the standard
  definition of a unital AF algebra (Bratteli).
* The two upstream interfaces, as `Statement`s. Lanes `nm-tww-02` (commutative)
  and `nm-tww-04` (AF) are authored in parallel and are not on disk yet.
  - `CommutativeQuasidiagonalTraceStatement`: every faithful tracial state on a
    separable unital commutative C⋆-algebra is quasidiagonal. This is the
    faithful-trace special case of lane `nm-tww-02`, which is stated for every
    tracial state. So the lane's theorem implies it (strictly weaker in logical
    strength), and it is true: states on `C(X)` are weak⋆ limits of rational
    averages of point evaluations, and those give unital ⋆-homomorphisms
    `C(X) → M_N` with the right normalized trace.
  - `AFQuasidiagonalTraceStatement`: every faithful tracial state on a
    C⋆-algebra with a `MultimatrixAFPresentation` is quasidiagonal. This is the
    faithful-trace special case of lane `nm-tww-04`. It is true: a trace on a
    multimatrix algebra is a convex combination of normalized block traces, so
    it is approximated by rational amplifications into `M_N`, and these extend
    to ucp maps on `A` by Arveson.

Once the upstream lanes land, each Statement follows from their endpoints by
restricting from all tracial states to faithful ones, plus a bridge from
lane 04's `AFPresentation` to `MultimatrixAFPresentation` if the two structures
differ.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

noncomputable section

/-! ## Multimatrix algebras and AF presentations -/

/-- **The multimatrix algebra** `⊕_{i<r} M_{k_i}(ℂ)`, the general
finite-dimensional C⋆-algebra. -/
abbrev Multimatrix (r : ℕ) (k : Fin r → ℕ) : Type :=
  ∀ i : Fin r, Matrix (Fin (k i)) (Fin (k i)) ℂ

/-- **A unital AF presentation** of a C⋆-algebra `A`: injective unital
⋆-homomorphisms `ιₙ : Bₙ → A` from multimatrix algebras whose ranges increase
and have dense union. -/
structure MultimatrixAFPresentation (A : Type) [CStarAlgebra A] where
  /-- The number of blocks of the `n`-th multimatrix algebra. -/
  blocks : ℕ → ℕ
  /-- The block sizes of the `n`-th multimatrix algebra. -/
  sizes : ∀ n : ℕ, Fin (blocks n) → ℕ
  /-- The unital ⋆-embeddings `ιₙ : Bₙ → A`. -/
  embed : ∀ n : ℕ, Multimatrix (blocks n) (sizes n) →⋆ₐ[ℂ] A
  /-- Each `ιₙ` is injective. -/
  injective : ∀ n : ℕ, Function.Injective ⇑(embed n)
  /-- The ranges increase. -/
  range_mono : ∀ n : ℕ, Set.range ⇑(embed n) ⊆ Set.range ⇑(embed (n + 1))
  /-- The union of the ranges is dense. -/
  dense : Dense (⋃ n : ℕ, Set.range ⇑(embed n))

/-! ## The upstream interfaces -/

/-- **Interface of lane `nm-tww-02`, faithful-trace case.** Every faithful
tracial state on a separable unital commutative C⋆-algebra is quasidiagonal.

This is true and is implied by lane `nm-tww-02`'s theorem, which covers every
tracial state. It is not proved here. -/
def CommutativeQuasidiagonalTraceStatement : Prop :=
  ∀ (A : Type) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
    (∀ a b : A, a * b = b * a) → ∀ τ : FaithfulTracialState A,
      Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

/-- **Interface of lane `nm-tww-04`, faithful-trace case.** Every faithful
tracial state on a C⋆-algebra with a unital AF presentation is quasidiagonal.

This is true and is implied by lane `nm-tww-04`'s theorem, which covers every
tracial state. It is not proved here. -/
def AFQuasidiagonalTraceStatement : Prop :=
  ∀ (A : Type) [CStarAlgebra A], MultimatrixAFPresentation A →
    ∀ τ : FaithfulTracialState A,
      Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

end

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.Multimatrix
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.MultimatrixAFPresentation
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.CommutativeQuasidiagonalTraceStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.AFQuasidiagonalTraceStatement
