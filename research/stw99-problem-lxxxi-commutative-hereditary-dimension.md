---
rg: 2
id: stw99-problem-lxxxi-commutative-hereditary-dimension
kind: claim
title: One-dimensional commutative hereditary shadows force nuclear dimension zero, one, or infinity (STW Problem LXXXI)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
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

The lower bound itself has perfect extension behavior:
`stw81-ctdim-extension-maximum` proves

```text
ctdim(E) = max(ctdim(I),ctdim(D))
```

for every separable extension.  Therefore any discrepancy in Problems
LXXXI--LXXXII occurs strictly above the continuous-trace shadow layer; it
cannot be explained by topological dimension appearing only after gluing.

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

The relationship is now internal and witness-level:
`stw81-finite-ideal-counterexample-forces-lxxxii-counterexample` proves that
every separable finite-ideal counterexample here contains, at its first
high-dimensional composition step, an LXXXII counterexample with both
endpoint dimensions at most one.
