---
rg: 2
id: lcs-tracial-ru-gap-equiv-nonhyperlinear
kind: claim
title: A tracially satisfiable but non-RU linear system is equivalent to a finitely presented nonhyperlinear group
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

Paddock--Slofstra, Proposition 5.8 (arXiv:2310.07901 / published version),
prove the equivalence:

```text
there exists a linear-system BCS that is tracially satisfiable
but not R^U-satisfiable

iff

there exists a nonhyperlinear finitely presented group.
```

For a linear system `Ax=b`, let `Gamma(A,b)` be its solution group and `J` its
central involution.  Their Lemma 5.7 gives the precise bridge used here:

- tracial satisfiability iff `J != 1` in `Gamma(A,b)`;
- `R^U`-satisfiability iff `J` is nontrivial in approximate representations.

Thus a tracial/non-`R^U` gap makes `J` an actual nontrivial group element that
is trivial in every approximate representation, so the solution group is
nonhyperlinear.  Conversely they embed an arbitrary finitely presented
nonhyperlinear witness into a solution group while preserving the marked
central involution.

This node is a source import, not a new proof.  It fixes the exact endpoint a
BCS/LCS groupification programme must reach: a **tracial-vs-approximate** gap,
not merely absence of an exact finite-dimensional representation.
