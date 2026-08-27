import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Analysis.ReducedGroupCStarDedekindFinite

/-!
# Stable finiteness from a faithful trace, and STW Problem VII ⟹ Problem IX(1)

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*,
arXiv:2506.10902, collect the open problems of the nuclear classification
programme.  Two of them are transcribed here, in the numbering of that list.

> **Problem VII.**  Is every separable nuclear stably finite C⋆-algebra
> quasidiagonal?

which the list attributes to Blackadar and Kirchberg, *Generalized inductive
limits of finite-dimensional C⋆-algebras*, Math. Ann. **307** (1997), 343--380,
Question 7.3.2, and

> **Problem IX(1).**  Is every separable nuclear C⋆-algebra with a faithful
> trace quasidiagonal?

Neither is asserted anywhere below.  Each is a named `Prop`, in the manner of
`Manuscript.NonMF.PriorWork.BlackadarKirchbergNFConverseInput`, and the two
declarations that conclude one of them carry the other as a leading binder.
What is proved unconditionally is the arrow between them: a positive answer to
Problem VII answers Problem IX(1), because a faithful trace forces stable
finiteness.

## The mathematics of the arrow

Let `τ` be a faithful tracial state on a unital C⋆-algebra `A` and let `τₙ` be
its amplification `M ↦ n⁻¹ ∑ᵢ τ (Mᵢᵢ)` to `Mₙ(A)`.  It is again a faithful
tracial state:

* *positivity and faithfulness*, because `(M⋆M)ᵢᵢ = ∑ⱼ (Mⱼᵢ)⋆ Mⱼᵢ`, so
  `τₙ (M⋆M)` is a sum of nonnegative reals, and a sum of nonnegative reals
  vanishes only when every summand does, which through faithfulness of `τ`
  kills every entry of `M`;
* *traciality*, because `τₙ (MN) = n⁻¹ ∑ᵢ ∑ⱼ τ (Mᵢⱼ Nⱼᵢ)` is symmetric in `M`
  and `N` once `τ (Mᵢⱼ Nⱼᵢ) = τ (Nⱼᵢ Mᵢⱼ)` is applied termwise and the two
  sums are exchanged.

Now let `v ∈ Mₙ(A)` satisfy `v⋆v = 1` and put `p := 1 - v v⋆`.  Then `p⋆ = p`
and `p² = p`, since `(v v⋆)(v v⋆) = v (v⋆ v) v⋆ = v v⋆`, and

    τₙ p = τₙ 1 - τₙ (v v⋆) = τₙ 1 - τₙ (v⋆ v) = τₙ 1 - τₙ 1 = 0

by traciality.  So `τₙ (p⋆ p) = τₙ p = 0`, and faithfulness gives `p = 0`, that
is `v v⋆ = 1`.  Every isometry in every matrix amplification is a unitary,
which is stable finiteness in the operator-algebraic sense.

## Nothing above is proved here a second time

All of it is already in the repository, and this module assembles rather than
reproves:

* `FaithfulTracialState.matrix` (`Analysis/FaithfulTracialMatrix.lean`) is the
  amplified faithful tracial state, carrying exactly the verifications above
  together with the normalization `τₙ 1 = 1`; the factor `n⁻¹` is there for
  that clause alone;
* `FaithfulTracialState.mul_star_eq_one_of_star_mul_eq_one`
  (`Analysis/FaithfulTracialState.lean`) is the isometry-is-unitary argument at
  a single algebra, and `FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one`
  is its composite with the amplification;
* `IsStablyFiniteCStarAlgebra` (`Analysis/ReducedGroupCStarStablyFinite.lean`)
  is the predicate, quantified over the `Fin (k + 1)` amplifications --- the
  empty amplification is the zero ring, where the identity holds for want of an
  entry, so restricting to nonempty index types costs nothing;
* `IsStablyFiniteCStarAlgebra.isStablyFiniteRing`
  (`Analysis/ReducedGroupCStarDedekindFinite.lean`) crosses the
  polar-decomposition bridge to mathlib's ring-theoretic `IsStablyFiniteRing`,
  which is Dedekind finiteness of every `Matrix (Fin n) (Fin n) A` and mentions
  neither the star operation nor the norm.

So `isStablyFiniteCStarAlgebra_of_faithfulTracialState` is a
specialization of the amplification to the indexing the predicate fixes, and
`isStablyFiniteRing_of_faithfulTracialState` is that composed with the bridge.
The second is the reading of "stably finite" that quantifies over plain matrix
rings; both are recorded so that a consumer needs neither to be restated.

## How the conclusion is transcribed

The problems conclude *quasidiagonal*; the statements below conclude
`IsNFAlgebra`, the repository's finite-local completely positive contractive
predicate (`Analysis/NFAlgebra.lean`).  Under the standing nuclearity
hypothesis the two agree, by the Blackadar--Kirchberg NF characterization of
the paper cited above (op. cit., §5.2): for separable C⋆-algebras, NF is
nuclear together with quasidiagonal, and for separable nuclear algebras NF, MF
and quasidiagonal coincide.  That characterization is *cited and not proved*
here --- `Manuscript.NonMF.PriorWork` carries the half of it the manuscript
consumes, as an explicit literature input --- so the transcription is a
statement about which proposition is being named, not a further theorem.

`IsNFAlgebra` carries separability inside it, so separability appears both as a
hypothesis and inside the conclusion.  It is kept as a hypothesis because that
is where the problems print it, and the redundancy is harmless: it makes the
hypotheses of the transcription match the hypotheses of the source.

Both problems are transcribed in the **unital** case, which is what
`CStarAlgebra` provides; the trace is a state, so `τ 1 = 1`.  Problem IX(1)
prints "has a faithful trace", and the transcription takes the trace as an
argument.  For a `Prop` conclusion the two are the same statement:
`Nonempty (FaithfulTracialState A) → P` and `FaithfulTracialState A → P` are
interderivable.

## What none of this bears on

`non_mf_groups_exist.tex` exhibits a separable stably finite C⋆-algebra that is
not MF, so not NF.  That is not a counterexample to Problem VII, and
`Manuscript.OneSidedMFRadical.ReducedCStarNotNuclear` is the machine-checked
reason: the witness is `C⋆_r(H)` for an infinite group `H` with Kazhdan's
property `(T)`, so `H` is not amenable and the algebra fails the completely
positive approximation property in the translation reading
`NuclearReducedCPAP`.  A non-nuclear algebra says nothing about a question
asked of nuclear ones.
-/

namespace GroupApproximation

namespace NinetyNineProblems

universe u

/-- **A faithful tracial state forces stable finiteness.**

Every isometry in every nonempty finite matrix amplification of `A` is a
unitary, because the amplified trace `FaithfulTracialState.matrix` is again a
faithful tracial state and the defect `1 - v v⋆` is a self-adjoint idempotent of
trace zero.  This is the implication that makes Problem VII imply
Problem IX(1).

The proof is the composite of two imported statements: the amplification
`FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one`, stated at an
arbitrary nonempty finite index type, and the adapter
`IsStablyFiniteCStarAlgebra.of_matrix_isometry_unitary`, which specializes it to
the `Fin (k + 1)` indexing the predicate fixes. -/
theorem isStablyFiniteCStarAlgebra_of_faithfulTracialState {A : Type u}
    [CStarAlgebra A] (τ : FaithfulTracialState A) :
    IsStablyFiniteCStarAlgebra A :=
  IsStablyFiniteCStarAlgebra.of_matrix_isometry_unitary
    fun n _ _ hn _ hv => τ.matrix_mul_star_eq_one_of_star_mul_eq_one n hn hv

/-- **A faithful tracial state forces ring-theoretic stable finiteness.**

The same conclusion in mathlib's vocabulary: every matrix ring
`Matrix (Fin n) (Fin n) A` over a unital C⋆-algebra carrying a faithful tracial
state is Dedekind finite, so a one-sided inverse there is two-sided.

This is the operator-algebraic statement above pushed across the
polar-decomposition bridge `IsStablyFiniteCStarAlgebra.isStablyFiniteRing`: an
element with a one-sided ring inverse is turned into an isometry by the
continuous functional calculus, and the trace argument makes that isometry a
unitary.  Neither the star operation nor the norm survives into the statement. -/
theorem isStablyFiniteRing_of_faithfulTracialState {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A) : IsStablyFiniteRing A :=
  (isStablyFiniteCStarAlgebra_of_faithfulTracialState τ).isStablyFiniteRing

/-- **Problem VII** of Schafhauser--Tikuisis--White, *Nuclear C⋆-algebras: 99
problems* (arXiv:2506.10902), attributed there to Blackadar--Kirchberg,
Math. Ann. **307** (1997), Question 7.3.2:

> Is every separable nuclear stably finite C⋆-algebra quasidiagonal?

Stated as a proposition and *not* asserted.  Nuclearity is the corpus-wide
completely positive approximation property
`CStarExactness.IsNuclearCStarAlgebra`; stable finiteness is the
operator-algebraic `IsStablyFiniteCStarAlgebra`, every isometry in every matrix
amplification being a unitary; and the conclusion is transcribed as
`IsNFAlgebra`, which agrees with quasidiagonality under the nuclearity
hypothesis by the cited Blackadar--Kirchberg characterization.  See the module
docstring for both transcription choices.

Every type and instance binder is inside the proposition, so a consumer must
carry it explicitly. -/
def ProblemVIIStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A],
    TopologicalSpace.SeparableSpace A →
      CStarExactness.IsNuclearCStarAlgebra A →
        IsStablyFiniteCStarAlgebra A → IsNFAlgebra A

/-- **Problem IX(1)** of Schafhauser--Tikuisis--White, *Nuclear C⋆-algebras: 99
problems* (arXiv:2506.10902):

> Is every separable nuclear C⋆-algebra with a faithful trace quasidiagonal?

Stated as a proposition and *not* asserted.  "Has a faithful trace" is rendered
by taking the trace as an argument, which for a `Prop` conclusion says the same
thing as assuming `Nonempty (FaithfulTracialState A)`.  The trace is a state,
so this is the unital reading of the problem.

The conclusion is transcribed as `IsNFAlgebra` exactly as in
`ProblemVIIStatement`, and for the same reason. -/
def ProblemIX1Statement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A],
    TopologicalSpace.SeparableSpace A →
      CStarExactness.IsNuclearCStarAlgebra A →
        FaithfulTracialState A → IsNFAlgebra A

/-- **Problem VII applied at one algebra with a faithful trace.**

A positive answer to Problem VII makes every separable nuclear C⋆-algebra
carrying a faithful tracial state NF, since the trace supplies the missing
hypothesis of stable finiteness through
`isStablyFiniteCStarAlgebra_of_faithfulTracialState`.  The cited statement stays
in the binder: nothing here discharges it. -/
theorem isNFAlgebra_of_faithfulTracialState_of_problemVIIStatement
    (h : ProblemVIIStatement.{u}) {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A)
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A)
    (τ : FaithfulTracialState A) : IsNFAlgebra A :=
  h A hsep hnuc (isStablyFiniteCStarAlgebra_of_faithfulTracialState τ)

/-- **Problem VII implies Problem IX(1).**

The reduction between the two printed questions, with no hypothesis beyond the
first: faithfulness of a tracial state forces stable finiteness, so the class of
algebras Problem IX(1) asks about sits inside the class Problem VII asks about.

This is the direction the containment of hypotheses gives, and it is the only
one offered.  Nothing here reduces Problem VII to Problem IX(1): that would ask
every separable nuclear stably finite C⋆-algebra to be brought under the
hypothesis of a *faithful* trace, which is a separate question and not one this
module takes a position on. -/
theorem problemIX1Statement_of_problemVIIStatement
    (h : ProblemVIIStatement.{u}) : ProblemIX1Statement.{u} := by
  intro A _instA hsep hnuc τ
  exact isNFAlgebra_of_faithfulTracialState_of_problemVIIStatement h hsep hnuc τ

end NinetyNineProblems

end GroupApproximation
