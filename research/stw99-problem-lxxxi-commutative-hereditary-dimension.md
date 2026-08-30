---
rg: 2
id: stw99-problem-lxxxi-commutative-hereditary-dimension
kind: claim
title: One-dimensional commutative hereditary shadows force nuclear dimension zero, one, or infinity (STW Problem LXXXI)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
  - research/artifacts/stw81-zero-dimensional-simple-field-audit-2026-08-30.md
  - research/artifacts/stw81-one-dimensional-field-audit-2026-08-30.md
  - research/artifacts/stw81-oinfinity-envelope-audit-2026-08-30.md
  - research/artifacts/stw81-one-dimensional-af-field-audit-2026-08-30.md
  - research/artifacts/stw81-continuous-af-field-audit-2026-08-30.md
  - research/artifacts/stw81-usc-af-fibre-field-audit-2026-08-30.md
---

**Problem LXXXI of Schafhauser--Tikuisis--White.**  Let `A` be a C-star
algebra such that, for every ideal `I` of `A` and every commutative
hereditary C-star subalgebra `C` of `A/I`,

```text
dim(Prim(C)) <= 1.
```

Must

```text
dim_nuc(A) belong to {0,1,infinity}?
```

The problem remains open in general.  The hypothesis rules out the standard
source of nuclear-dimension lower bounds—high-dimensional commutative
hereditary subalgebras in quotients—but it is unknown whether a genuinely
noncommutative finite value at least two can remain.

For separable algebras the hypothesis now has an exact invariant
reformulation.  `stw81-continuous-trace-shadow-invariant` defines `ctdim(A)`
as the supremal spectrum dimension among continuous-trace subquotients and
proves

```text
ctdim(A) <= dim_nuc(A),
LXXXI shadow hypothesis iff ctdim(A) <= 1.
```

Thus the question is precisely whether this canonical type-I lower bound
can stay at most one while nuclear dimension takes a finite value at least
two.

The terminology is exact: `stw81-ctdim-equals-type-i-topological-dimension`
proves that `ctdim` agrees with Brown--Pedersen topological dimension on
every separable type-I algebra.  It is also stable under Morita equivalence
by `stw81-ctdim-morita-invariance`, so both the invariant and the original
shadow hypothesis survive stabilization.

The lower bound itself has perfect extension behavior:
`stw81-ctdim-extension-maximum` proves

```text
ctdim(E) = max(ctdim(I),ctdim(D))
```

for every separable extension.  Therefore any discrepancy in Problems
LXXXI--LXXXII occurs strictly above the continuous-trace shadow layer; it
cannot be explained by topological dimension appearing only after gluing.

This exact behavior persists through arbitrary directed hereditary
exhaustions.  `stw81-ctdim-directed-hereditary-continuity` proves that if a
separable algebra is the closure of an upward-directed union of hereditary
subalgebras `B_lambda`, then

```text
ctdim(A) = sup_lambda ctdim(B_lambda).
```

Thus the shadow hypothesis is both preserved and reflected by arbitrarily
indexed inductive limits whose injective connecting maps have hereditary
images, provided the limit is separable.  No countability, ordinal
continuity, or cofinality assumption is needed: separability extracts an
increasing sequence which is already dense.  No assertion is made for
arbitrary injective connecting maps without hereditary images.

The counterexample search can also be normalized:
`stw81-counterexamples-reduce-to-stable-and-unital` shows that any separable
counterexample produces both a stable witness and a unital witness, without
changing its nuclear dimension.  These are separate normal forms; no
nonzero algebra is asserted to be simultaneously stable and unital.

## Attempts

`stw81-separable-subhomogeneous-positive` proves the assertion for separable
subhomogeneous algebras by extracting local rank-one commutative corners from
every homogeneous stratum.  Beyond type I structure, there need not be local
matrix-bundle charts from which to extract such a corner.  The extension
route is Problem LXXXII: a general maximum formula, combined with the simple
nuclear-dimension dichotomy, would settle finite-ideal separable cases, but
the required color reuse remains open.

The rank-one method now extends beyond uniformly finite-dimensional fibres.
`stw81-continuous-trace-positive` proves the assertion for all separable
continuous-trace algebras, including infinite-dimensional compact-operator
bundles.  More generally,
`stw81-type-i-topological-dimension-collapse` shows that the hypothesis
forces `topdim(A)<=1` for every separable type-I algebra.  Thus a type-I
counterexample would have to separate nuclear dimension from
Brown--Pedersen topological dimension at the first possible value; merely
adding high-dimensional type-I strata cannot produce one.

A genuinely non-type-I extension class is also closed.
`stw81-full-af-by-oinfinity-extensions-are-one-dimensional` proves that a
full extension with separable stable AF ideal and nonzero separable nuclear
O-infinity-stable quotient has nuclear dimension exactly one, by Evington's
specialized full-extension theorem.  The `ctdim` lower bound then makes the
LXXXI shadow hypothesis automatic.  This includes every Toeplitz--Cuntz
algebra `T_n`, `2<=n<infinity`.  Fullness, stability of the ideal, and
O-infinity-stability of the quotient are essential hypotheses of the
imported theorem; no instance of Problem LXXXII is assumed.

A new infinite-ideal field class is now closed as well.
`stw81-zero-dim-simple-fields-obey-trichotomy`
proves that a separable locally trivial field over a zero-dimensional base
with simple nuclear fibres has nuclear dimension equal to the supremum of
the fibre dimensions, hence `0`, `1`, or `infinity`.  Its commutative
hereditary shadows are automatically zero-dimensional.  The mechanism is
clopen colour reuse: a disjoint clopen refinement reduces the algebra to
AF-base tensors of the simple fibres, without an extension-gluing colour.

There is also a sharp warning against using the whole primitive spectrum.
`stw81-shadow-hypothesis-does-not-bound-primitive-spectrum` shows that
`C_0(X) tensor O_2` has primitive spectrum `X` and nuclear dimension one,
but no nonzero commutative hereditary subalgebra in any quotient.  Thus
`dim Prim(A)` can be infinite under the strongest possible shadow bound.
Only the type-I loci, and their boundary interaction with non-type-I
strata, are visible to the hypothesis.

The field theorem now reaches one-dimensional bases under a sharp fibre
dichotomy.  `stw81-one-dim-elementary-oinfty-fields-have-dim-one` proves
the assertion for locally trivial simple-fibre fields whose fibres are
elementary or O-infinity-stable.  The elementary locus is continuous
trace; fibrewise O-infinity-stability globalizes over the finite-dimensional
base and then forces nuclear dimension one.  Both loci are clopen, and
the shadows live entirely on the elementary side.

The previous clopen method cannot handle the remaining stably finite
fibres.  `stw81-connected-base-blocks-clopen-colour-reuse` proves that a
connected nontrivial base has no finite-dimensional subalgebras of
`C(X)` beyond the constants, so the AF-base approximation used in the
zero-dimensional theorem fails exactly there.  For one-dimensional
stably finite non-elementary fibres, fibrewise Z-stability globalizes but
the needed nonsimple nuclear-dimension-one theorem is unavailable; naive
base/fibre colour multiplication gives three.

There is now a first stably finite non-elementary exception to that
obstruction.  `stw81-one-dim-simple-af-fields-have-dim-one`
proves directly that a locally trivial field over a one-dimensional base
with infinite-dimensional simple unital AF fibre (in particular a UHF
fibre) has nuclear dimension at most one.  The proof samples sections in a
two-coloured base cover and absorbs the entire fibre approximation into
finite-dimensional AF subalgebras, so there is no extra fibre colour.  Such
fields have no nonzero commutative hereditary subalgebras in any quotient.

The AF-fibre dimension bound now holds in full upper-semicontinuous
generality.  `stw81-af-fibre-fields-have-base-bound` proves that every
separable `C_0(X)`-algebra over a second-countable locally compact
finite-dimensional base, with arbitrary possibly nonunital and nonsimple AF
fibres, satisfies `dim_nuc(A)<=dim(X)`.  Finite-dimensional fibre
subalgebras lift exactly over closed neighborhoods by semiprojectivity;
upper semicontinuity, rather than continuity, is enough to shrink the local
error bound, and central cutoffs give c.p.c. order-zero return maps.  The
  same fibrewise argument supplies the shadow-free conclusion when the fibres
  are simple and non-elementary.  Thus over a one-dimensional base the LXXXI
  conclusion holds for arbitrary upper-semicontinuous fields of simple
  non-elementary AF algebras.  The remaining stably finite field frontier
  begins with non-AF fibres, not with discontinuity or nonunitality of the AF
  field.

There is now also a base-free absorption class with an exact dichotomy.
`stw81-oinfinity-envelopes-have-dimension-one-or-infinity` proves that for
every nonzero separable algebra `B`,

```text
dim_nuc(B tensor O_infinity)=1        if B is nuclear,
dim_nuc(B tensor O_infinity)=infinity otherwise.
```

Every quotient of this envelope has no nonzero commutative hereditary
subalgebra: O-infinity-absorption passes first to the quotient and then to
the hereditary subalgebra, where commutativity would contradict strong pure
infiniteness.  Nuclearity is reflected back to `B` by a slice-map completely
positive retraction, so the infinite half of the formula does not conceal an
exactness assumption.  This class permits arbitrary ideal and primitive-space
complexity and is independent of the zero- and one-dimensional field results.

The relationship is now internal and witness-level:
`stw81-finite-ideal-counterexample-forces-lxxxii-counterexample` proves that
every separable finite-ideal counterexample here contains, at its first
high-dimensional composition step, an LXXXII counterexample with both
endpoint dimensions at most one.
