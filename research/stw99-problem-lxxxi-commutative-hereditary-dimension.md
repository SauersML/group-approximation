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

## Attempts

`stw81-separable-subhomogeneous-positive` proves the assertion for separable
subhomogeneous algebras by extracting local rank-one commutative corners from
every homogeneous stratum.  Beyond type I structure, there need not be local
matrix-bundle charts from which to extract such a corner.  The extension
route is Problem LXXXII: a general maximum formula, combined with the simple
nuclear-dimension dichotomy, would settle finite-ideal separable cases, but
the required color reuse remains open.
