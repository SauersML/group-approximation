import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# The factorization property makes a group hyperlinear

Brown, *Invariant means and finite representation theory of C⋆-algebras*,
Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 3.1.7, lists conditions
on a trace that are equivalent to amenability; `(1) ⟹ (2)` there says that an
amenable trace on `C⋆(G)` gives an embedding of the group von Neumann algebra
`L(G)` into `R^ω`, so that `G` is hyperlinear.  Together with Kirchberg's
formulation of the factorization property --- and with Brown's Theorem 4.1.9,
which is what lets `HasFactorizationProperty` be stated at the trace ---  that
reads: **a countable group with the factorization property is hyperlinear.**

That implication is `BrownAmenableTraceHyperlinearInput`, an assumed input.
This file states it, consumes it once, and proves the half of it that is
already available, so that the gap is visible as a single named step.

## Where exactly the gap is

Amenability of the canonical trace already gives, unconditionally, that the
trace is a **hyperlinear trace** in Shulman's sense
(`isHyperlinearTrace_canonicalMaximal_of_hasFactorizationProperty` below, whose
content is `NinetyNineProblems.isHyperlinearTrace_of_isAmenableTrace`): matrix
models `φₙ : C⋆(G) → M_{kₙ}` with the three defects small in the normalized
Hilbert--Schmidt norm and `tr φₙ → τ`.

What is missing is the passage from there to `IsHyperlinear G`, which asks for
*unitary* matrices.  The models coming from an amenable trace are unital
completely positive, so `xₙ(g) := φₙ(u_g)` satisfies
`‖xₙ(g)ᴴ xₙ(g) − 1‖₂ → 0`, but the matrices themselves are not unitary, and
`IsHyperlinear`'s `isUnitary` field is not negotiable.

## What a proof needs, precisely

One lemma, at a single matrix:

```text
exists_unitary_hsNorm_sub_le (Y : FiniteModel) (x : Matrix Y Y ℂ) :
    ∃ u ∈ Matrix.unitaryGroup Y ℂ, hsNorm Y (u - x) ≤ hsNorm Y (xᴴ * x - 1)
```

Write `x = u |x|` with `u` unitary --- available in finite dimensions, the
partial isometry being extended across the kernel.  Then `u − x = u(1 − |x|)`,
and `hsNorm` is unitarily invariant
(`hsNorm_unitary_mul_mul`, `Analysis/PreliminaryInequalitiesPrinted.lean`), so
`‖u − x‖₂ = ‖1 − |x|‖₂ ≤ ‖1 − xᴴx‖₂` by the eigenvalue comparison
`|1 − √t| ≤ |1 − t|` for `t ≥ 0`.

**No contraction hypothesis is needed.**  `|1 − t| = |1 − √t| (1 + √t)` and
`1 + √t ≥ 1`, so the comparison holds at every nonnegative eigenvalue of
`xᴴx`, not only at those in `[0, 1]`.  So the lemma is about an arbitrary
square matrix, and the ucp contractivity of the models is not spent on it.

The **operator-norm** polar correction the repository already carries
(`Quasidiagonal`'s route through `Analysis/PolarLiftingGeneralCStar.lean`,
`polarUnitary x = x (x⋆x)^{-1/2}` with `norm_polarUnitary_sub_le`) does **not**
apply: it needs `‖x⋆x − 1‖ ≤ 1/2` in the operator norm, and a Hilbert--Schmidt
defect gives no operator-norm control at all --- a projection of rank `k/2` has
`‖p‖₂ = 1/√2` and `‖p‖ = 1`.  The two estimates are different theorems.

Once `Analysis/HilbertSchmidtPolarCorrection.lean` supplies the lemma above,
the rest is bookkeeping already present in the repository --- the Gram defect
from `Quasidiagonal.ucp_map_star` and `AmenableTraceModel.tendsto_mul_hs`, the
separation clause from `hsDistSq_of_unitary` against the trace clause, and the
finite-test-set quantifier from `ShulmanTrace.eventually_le_of_tendsto_zero`
--- and `BrownAmenableTraceHyperlinearInput` becomes a theorem, at which point
every declaration below that carries it as a binder loses the binder.
-/

namespace GroupApproximation
namespace NinetyNineProblems

universe u

/-! ## The unconditional half -/

/-- **The factorization property makes the canonical trace hyperlinear**, in
Shulman's sense.  Unconditional, and immediate: the factorization property
*is* amenability of that trace, and an amenable trace is a hyperlinear trace
(`isHyperlinearTrace_of_isAmenableTrace`) --- the u.c.p. models weaken to
Hilbert--Schmidt approximation data, with the tracial-state datum supplied by
`ShulmanTrace.canonicalMaximalTracialState`.

This is exactly as far as the repository gets without new analysis; the
remaining step is about the *group*, not the trace. -/
theorem isHyperlinearTrace_canonicalMaximal_of_hasFactorizationProperty
    (G : Type u) [Group G] (h : HasFactorizationProperty G) :
    ShulmanTrace.IsHyperlinearTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  isHyperlinearTrace_of_isAmenableTrace
    ⟨ShulmanTrace.canonicalMaximalTracialState G, fun _ ↦ rfl⟩ h

/-! ## Brown's implication, as a typed input -/

/-- **Brown's Theorem 3.1.7 `(1) ⟹ (2)`, as a typed input.**

> Brown, Mem. AMS **184** (2006), no. 865, Theorem 3.1.7: an amenable trace on
> a separable unital C⋆-algebra gives an embedding of the associated finite
> von Neumann algebra into `R^ω`.  At the canonical trace of `C⋆(G)` --- which
> is amenable exactly when `G` has Kirchberg's factorization property, Brown's
> Theorem 4.1.9 --- this says that `L(G)` embeds in `R^ω`, which is
> hyperlinearity of `G`.

No inhabitant is constructed.  The missing step is named and analyzed in the
module docstring: it is the Hilbert--Schmidt polar correction, and nothing
weaker will do, because `IsHyperlinear` demands genuinely unitary models while
an amenable trace supplies only approximately unitary ones.

It is a structure rather than a bare implication so that consuming it leaves a
visible binder in the type of every theorem that does. -/
structure BrownAmenableTraceHyperlinearInput : Prop where
  /-- A countable group with the factorization property is hyperlinear. -/
  isHyperlinear : ∀ (G : Type u) [Group G] [Countable G],
    HasFactorizationProperty G → IsHyperlinear G

/-- **A countable group with the factorization property is hyperlinear**,
granted Brown's implication.

The whole cost is the leading binder `b`.  Read against
`not_forall_sofic_hasFactorizationProperty` of
`Manuscript/NinetyNineProblems/FactorizationProperty.lean`, this places the
factorization property strictly between residual finiteness and
hyperlinearity: it implies hyperlinearity, and Thom's examples show
hyperlinearity does not imply it. -/
theorem isHyperlinear_of_hasFactorizationProperty
    (b : BrownAmenableTraceHyperlinearInput.{u}) (G : Type u) [Group G]
    [Countable G] (h : HasFactorizationProperty G) : IsHyperlinear G :=
  b.isHyperlinear G h

/-- The literal group of `Manuscript/NinetyNineProblems/ProblemX.lean`, for
completeness of the picture: its open clause would give hyperlinearity.

This says nothing new about `E`, which is hyperlinear outright because it is
sofic (`LiteralSoficAssembly.markedGroup_isHyperlinear`).  It is recorded to
make the direction of the open clause visible: `LiteralFactorizationProperty`
is *stronger* than anything already known about `E`, so no argument runs
backwards from hyperlinearity to it. -/
theorem markedGroup_isHyperlinear_of_literalFactorizationProperty
    (b : BrownAmenableTraceHyperlinearInput.{0})
    (h : LiteralFactorizationProperty) :
    IsHyperlinear LiteralNonMFPresentation.MarkedGroup :=
  isHyperlinear_of_hasFactorizationProperty b LiteralNonMFPresentation.MarkedGroup
    (literalFactorizationProperty_iff.mp h)

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms isHyperlinearTrace_canonicalMaximal_of_hasFactorizationProperty
#audit_axioms BrownAmenableTraceHyperlinearInput
#audit_axioms isHyperlinear_of_hasFactorizationProperty
#audit_axioms markedGroup_isHyperlinear_of_literalFactorizationProperty
