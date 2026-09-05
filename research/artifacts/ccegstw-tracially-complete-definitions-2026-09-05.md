# Tracially complete C*-algebras: the definitions STW Problem XXII quotes

Verbatim source pins for the notions target 2 is *about*. Landed 2026-09-05
because the campaign's pinned-source rule was not in fact satisfied: lane
`xxii-factoriality` grepped `research/`, `research/artifacts/`, `notes/` and
`metadata/` and found **no definition of "factorial" or "tracially complete"
anywhere in this repository**. The only thing standing in for one was a single
sentence in §6 of `stw22-trace-problem-counterexample-audit-2026-08-31.md`:

> "Since the uniform tracial completion with its designated compact trace face
> is factorial in the tracially-complete sense … the example also refutes the
> equivalent factorial-tracially-complete formulation."

That sentence *asserts* precisely the thing that had to be proved, which is how
the Lean endpoint came to omit factoriality from its conjunction for a whole
day. So the definitions are recorded here, from the source, and the endpoint is
now checkable against them by a reader who does not have the paper open.

**Source.** Carrión, Castillejos, Evington, Gabe, Schafhauser, Tikuisis, White,
*Tracially complete C\*-algebras*, arXiv:2310.20594**v6**. Fetched 2026-09-05
by `xxii-factoriality`, who flagged the fetch as a deviation from "pinned
sources only" — correctly, since there was nothing in-repo to pin.

## The definitions

**Definition 3.4.** A *tracially complete C\*-algebra* is a pair `(ℳ, X)` where
`ℳ` is a C\*-algebra and `X ⊆ T(ℳ)` is a compact convex set such that

1. `X` is a faithful set of traces on `ℳ`, and
2. the unit ball of `ℳ` is `‖·‖_{2,X}`-complete.

**Definition 3.13.** A tracially complete C\*-algebra `(ℳ, X)` is *factorial*
if `X` is a **closed face** of `T(ℳ)`.

**Proposition 3.14.** Factorial ⟺ `π_τ(ℳ)''` is a factor for every
`τ ∈ ∂ₑX`.

**Proposition 3.15.** If `(ℳ, X)` is factorial, `X` is precisely the set of
`‖·‖_{2,X}`-continuous traces on `ℳ`.

**Proposition 3.23(iv).** The completion `(Ā^X, X̃)` is factorial **if and only
if `X` is a face in `T(A)`**.

**Question 1.1** (this is STW Problem XXII). "Let `(ℳ, X)` be a factorial
tracially complete C\*-algebra. Are all traces on `ℳ` automatically
`‖·‖_{2,X}`-continuous? Equivalently, is the inclusion `X ⊆ T(ℳ)` an equality?"

§3.2, in prose: "The examples of greatest interest — uniform tracial
completions of C\*-algebras — are automatically factorial."

## Why factoriality is a theorem here and not a hypothesis

Our `X` is the whole of `T(A)`, and a set is trivially a face of itself. So
Proposition 3.23(iv) gives factoriality of the completion outright, by its
forward half alone.

This closes the gap `audit-gate` opened, and it closes it by neither of the two
routes they proposed: `IsBauerSimplex` is not needed, the centre computation in
`STW22AntipodalBlockComplexCenter` is not needed, and no W\*-bundle over `∂ₑX`
is needed. Recorded because those three were reasonable guesses and someone
will otherwise make them again.

Formalized in `Analysis/TraciallyCompleteCStar.lean` (the definitions, over the
project's bundled `TracialState`, plus `compactSpace_tracialState` — weak-\*
compactness of `T(A)` by Tychonoff, which Definition 3.4 requires and which the
repo did not have), `STW22FactorialCore.lean`
(`isFaceTraceSet_designatedTraces` is factoriality), and
`STW22TraciallyCompletePair.lean` (Prop 3.23(i) and the bundled pair).
