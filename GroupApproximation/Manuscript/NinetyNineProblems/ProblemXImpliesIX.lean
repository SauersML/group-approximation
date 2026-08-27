import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Sofic.MFTraceCoronaBridge
import GroupApproximation.Manuscript.NonMF.PriorWorkBlackadarKirchberg
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX
import GroupApproximation.Manuscript.NinetyNineProblems.StablyFinite

/-!
# STW Problem X(1) ⟹ Problem IX(1)

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*,
arXiv:2506.10902, remark before Problem X that a positive answer to

> **Problem X(1).**  Is every amenable trace quasidiagonal?

gives a positive answer to

> **Problem IX(1).**  Is every separable nuclear C⋆-algebra with a faithful
> trace quasidiagonal?

`problemIX1Statement_of_problemX1Statement` is that remark.  `ProblemX1Statement`
is `Manuscript.NinetyNineProblems.ProblemX`'s transcription and
`ProblemIX1Statement` is `Manuscript.NinetyNineProblems.StablyFinite`'s; neither
is asserted here, and the theorem carries both the second statement's premises
and every literature input in its binders.

## The chain, and who owns each link

Let `A` be separable and nuclear with a faithful tracial state `τ`.

1. **`τ` is an amenable trace.**  Nuclearity factors the identity approximately
   through matrix algebras by unital completely positive maps, and those maps
   are approximately multiplicative in the `2`-norm of any trace.  Connes and
   Haagerup by way of Choi--Effros; Brown--Ozawa, *C⋆-algebras and
   Finite-Dimensional Approximations*, Theorem 6.2.7.  **Cited**, as the binder
   `QuasidiagonalMF.NuclearAmenableTraceInput`.
2. **`τ` is a quasidiagonal trace.**  This is Problem X(1), the binder `hX`.
3. **`A` is MF.**  A faithful quasidiagonal trace makes the corona
   homomorphism of its own models injective.  **Proved below**, unconditionally
   --- see the next section.
4. **`A` is NF.**  A separable nuclear MF C⋆-algebra is NF, which is the
   converse half of the Blackadar--Kirchberg characterization,
   Math. Ann. **307** (1997), 343--380.  **Cited**, as the binder
   `Manuscript.NonMF.PriorWork.BlackadarKirchbergNFConverseInput`.

Only steps 1 and 4 are citations, and both were already typed in this
repository before this module; nothing new is assumed here.  Step 2 is the
problem being reduced.  Step 3 is the one that had to be proved.

## Step 3, which is new here

The classical statement is Brown's, *Invariant means and finite representation
theory of C⋆-algebras*, Mem. Amer. Math. Soc. **184** (2006), no. 865, §4.1: an
algebra with a faithful quasidiagonal trace is MF.  It enters below as a
theorem and not as a citation, because the repository already carries every
piece of the construction:

* `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` weakens the quasidiagonal
  models to Shulman's `MFTraceModel`, using the contractivity of unital
  completely positive maps into matrices --- which is `Quasidiagonal.ucpContractive`,
  a **theorem** of `Analysis/UCPContractiveMatrix.lean`, so it enters as a term
  and leaves no binder;
* `ShulmanTrace.MFTraceModel.exists_shift` discards the finitely many empty
  models a unital trace tolerates;
* `ShulmanTrace.MFTraceModel.coronaHom` turns the asymptotically multiplicative
  models into an exact `⋆`-homomorphism into the norm-matrix corona, the
  defects being null sequences and so zero in the quotient;
* `ShulmanTrace.MFTraceModel.eq_of_coronaHom_eq` is the trace clause: elements
  with the same corona image have `τ`-values that agree, because the normalized
  trace is contractive for the operator norm;
* `MFAlgebraDimension.hasMFEmbedding_iff` normalizes the dimension sequence,
  which `HasMFEmbedding` requires to be strictly increasing and a trace model
  has no reason to supply.

What was missing was the half-line that uses **faithfulness**:
`coronaHom_injective_of_faithful` below.  If `Φ x = 0` then `Φ (x⋆x) = 0`, so
`τ (x⋆x) = τ 0 = 0`, so `x = 0`.  The trace clause is consumed at `x⋆x` rather
than at `x` --- that is the whole role of faithfulness, and it is why a merely
faithful *state* would not do.

The repository's existing route from an MF trace to MF-ness
(`ShulmanTrace.isOperatorMF_of_isMFTrace`, `Analysis/TikuisisWhiteWinter.lean`'s
`isOperatorMF_of_isQuasidiagonalCanonicalTrace`) runs through the *group*
predicate `IsOperatorMF` and the canonical maximal trace, so it does not apply
to an arbitrary C⋆-algebra.  `isMFAlgebra_of_isQuasidiagonalTrace` is the
algebra-level statement, and it is stated at the same corona machinery.

## What this does not do

It does not answer either problem, and it does not weaken the other reduction
already recorded: `StablyFinite.problemIX1Statement_of_problemVIIStatement`
derives Problem IX(1) from Problem VII with no literature input at all, because
a faithful trace forces stable finiteness outright.  So Problem IX(1) now has
two named sufficient conditions in this development, and they are of quite
different cost --- the one below buys IX(1) from a question about *all* amenable
traces, at the price of two citations.
-/

namespace GroupApproximation

namespace NinetyNineProblems

universe u

/-! ## A faithful trace makes the corona homomorphism injective -/

/-- **Faithfulness is exactly injectivity of the corona homomorphism.**

If the corona image of `x` vanishes, then so does the corona image of `x⋆x`,
whose `τ`-value the trace clause of the model therefore pins to `τ 0 = 0`;
faithfulness of `τ` then makes `x` itself zero.

The trace clause is applied at `x⋆x` and not at `x`, which is the reason a
faithful *tracial state* is asked for rather than a faithful state: only the
positive elements carry the detection property that
`FaithfulTracialState.eq_zero_of_map_star_mul_self_eq_zero` records. -/
theorem coronaHom_injective_of_faithful {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A)
    (M : ShulmanTrace.MFTraceModel (fun a : A ↦ τ a))
    [∀ n, Nonempty (M.space n)] :
    Function.Injective M.coronaHom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hstar : M.coronaHom (star x * x) = M.coronaHom 0 := by
    simp only [map_mul, map_star, hx, star_zero, mul_zero, map_zero]
  have hzero : τ (star x * x) = τ 0 := M.eq_of_coronaHom_eq hstar
  exact τ.eq_zero_of_map_star_mul_self_eq_zero (hzero.trans τ.map_zero)

/-- **A separable C⋆-algebra with a faithful quasidiagonal trace is MF.**

The algebra-level form of the argument in Brown, Mem. Amer. Math. Soc. **184**
(2006), no. 865, §4.1, assembled from the repository's own corona machinery and
assuming nothing: the quasidiagonal models weaken to an `MFTraceModel`, the
finitely many empty models are shifted away, the resulting corona
`⋆`-homomorphism is injective by `coronaHom_injective_of_faithful`, and the
dimension sequence is normalized to a strictly increasing one by
`MFAlgebraDimension.hasMFEmbedding_iff`.

Separability is a hypothesis rather than a conclusion because `IsMFAlgebra`
carries it; the trace argument says nothing about it. -/
theorem isMFAlgebra_of_isQuasidiagonalTrace {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) (τ : FaithfulTracialState A)
    (hqd : Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)) :
    IsMFAlgebra A := by
  have hmf : ShulmanTrace.IsMFTrace (fun a : A ↦ τ a) :=
    Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace
      (IsTracialState.of_bundled τ.toTracialState)
      Quasidiagonal.ucpContractive hqd
  obtain ⟨-, ⟨M⟩⟩ := hmf
  obtain ⟨M', hpos⟩ := M.exists_shift τ.apply_one
  have hne : ∀ n, Nonempty (M'.space n) := fun n ↦ Fintype.card_pos_iff.mp (hpos n)
  letI : ∀ n, Nonempty (M'.space n) := hne
  have hunrestricted : MFAlgebraDimension.HasUnrestrictedMFEmbedding A :=
    ⟨M'.space, hne, hpos, M'.coronaHom, coronaHom_injective_of_faithful τ M'⟩
  exact ⟨hsep, (MFAlgebraDimension.hasMFEmbedding_iff A).mpr hunrestricted⟩

/-! ## The reduction -/

/-- **Problem X(1) applied at one separable nuclear algebra with a faithful
trace.**

The four links of the module docstring, in order: the Connes--Haagerup input
makes the faithful trace amenable, Problem X(1) makes it quasidiagonal,
`isMFAlgebra_of_isQuasidiagonalTrace` makes the algebra MF, and the
Blackadar--Kirchberg converse makes it NF.

The bundled `TracialState` that Problem X(1) quantifies over is
`FaithfulTracialState.toTracialState`, whose underlying function is `τ`'s by
`FaithfulTracialState.coe_toTracialState` --- a definitional equality, so the
two amenability statements are the same proposition. -/
theorem isNFAlgebra_of_faithfulTracialState_of_problemX1Statement
    (connes : QuasidiagonalMF.NuclearAmenableTraceInput.{u})
    (bk : Manuscript.NonMF.PriorWork.BlackadarKirchbergNFConverseInput.{u})
    (hX : ProblemX1Statement.{u}) {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A)
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A)
    (τ : FaithfulTracialState A) : IsNFAlgebra A := by
  have hamen : Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) :=
    connes.amenableTrace A inferInstance hnuc τ
  have hqd : Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
    hX A τ.toTracialState hamen
  exact Manuscript.NonMF.PriorWork.blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra
    bk hnuc (isMFAlgebra_of_isQuasidiagonalTrace hsep τ hqd)

/-- **Problem X(1) implies Problem IX(1)**, the reduction Schafhauser, Tikuisis
and White record in the sentence before Problem X.

Both citations stay in the binders, and they are the only two: the passage from
a quasidiagonal trace to MF-ness of the algebra is proved rather than cited, and
the contractivity of unital completely positive matrix maps that it consumes is
a theorem of this repository.

The hypotheses of Problem IX(1) are used unevenly, which is worth seeing:
nuclearity is used twice --- once to make the trace amenable and once for the
Blackadar--Kirchberg converse --- while separability is used only at the end,
where `IsMFAlgebra` and `IsNFAlgebra` both carry it. -/
theorem problemIX1Statement_of_problemX1Statement
    (connes : QuasidiagonalMF.NuclearAmenableTraceInput.{u})
    (bk : Manuscript.NonMF.PriorWork.BlackadarKirchbergNFConverseInput.{u})
    (hX : ProblemX1Statement.{u}) : ProblemIX1Statement.{u} := by
  intro A _instA hsep hnuc τ
  exact isNFAlgebra_of_faithfulTracialState_of_problemX1Statement connes bk hX
    hsep hnuc τ

end NinetyNineProblems

end GroupApproximation
