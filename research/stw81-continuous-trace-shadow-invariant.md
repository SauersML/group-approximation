---
rg: 2
id: stw81-continuous-trace-shadow-invariant
kind: claim
title: Continuous-trace subquotients exactly encode the LXXXI shadow hypothesis
distinct_from:
  stw81-type-i-topological-dimension-collapse: that specializes the shadow hypothesis to Brown--Pedersen dimension for type-I algebras; this claim gives an exact reformulation for every separable C-star algebra.
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

For a separable C-star algebra `A`, define

```text
ctdim(A) = sup { dim(Prim(D)) : D is a continuous-trace subquotient of A },
```

where a subquotient has the form `J/I` for ideals `I subset J` of `A`, and
the supremum is declared zero if there are no nonzero continuous-trace
subquotients.  Then

```text
ctdim(A) <= dim_nuc(A).
```

Moreover, the hereditary commutative-shadow hypothesis in Problem LXXXI is
equivalent to

```text
ctdim(A) <= 1.
```

Consequently, the separable form of Problem LXXXI asks exactly whether
finite nuclear dimension can exceed one when its continuous-trace
subquotient lower bound does not exceed one.
