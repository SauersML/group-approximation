---
rg: 2
id: llp-failure-has-three-dimensional-hyperrigid-witness
kind: claim
title: LLP failure in a finitely generated C-star algebra has a three-dimensional hyperrigid LP witness
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  triangle-colimit-llp-reduces-to-relator-local-splitting: that is a positive equivalence for one triangle-colimit quotient; this is a universal compression theorem for a NEGATIVE LLP witness after the candidate algebra is fixed.
  llp-hole-via-triangle-relator-local-sections: that asks for local ucp sections proving LLP; this says how small a counterexample can be if those sections do not exist, but supplies no positive section.
---

**THEOREM (Harris, arXiv:2607.11001v1, Theorem 2.4 and Corollary
3.5).**  Let `A` be a finitely generated unital C-star algebra without
LLP.  Choose `n` unitary generators.  Harris constructs self-adjoint
elements `D,G in M_(n+2)(A)` such that

```text
S=span{I,D,G} subset M_(n+2)(A)                       (H3D1)
```

is a three-dimensional hyperrigid operator system, generates the full
matrix algebra `M_(n+2)(A)`, and does not have the operator-system lifting
property.

The construction is structured, not a dimension-only existence statement:
`D` is diagonal with distinct scalar entries and `G` is a sparse
self-adjoint matrix whose labeled entries include the chosen unitary
generators.  Hyperrigidity turns any ucp extension agreeing on `(H3D1)`
into the original star representation.  If `S` had LP, the tensorial
hyperrigidity argument of Proposition 3.4 would force `A` to have LLP,
giving Corollary 3.5.

Thus every negative answer to either the full-completion LLP frontier or
`explicit-proper-d-completion-with-llp-exists` has a three-dimensional
operator-system witness after one fixed matrix amplification.  This
materially narrows symbolic and numerical refutation searches.  More
importantly, the converse is exact for this system: ambient LLP restricts
to LP on the finite-dimensional subsystem, while Proposition 3.4(2) and
matrix/corner permanence give **LP of `S` implies LLP of `A`**.  Thus
`LP(S) <=> LLP(A)`.  Combined with Paulsen--Rahaman--Samei, this gives the
positive three-dimensional closing criterion in
`lp-of-harris-generator-system-forces-nonhyperlinear`.

It does **not** make LLP decidable and does not provide a uniform finite
semidefinite certificate for failure: the LP failure of `S` still
quantifies over a quotient and a nonliftable ucp map.  It is therefore a
negative-certificate normal form and a sharply localized positive target,
not by itself a proof of LP or LLP.


Scherer, arXiv:2607.04274v1, is the explicit model case
`S=span{1,D,K} subset M_4(C^*_r(F_2))`.  Harris's later theorem is the
reusable generalization.  No exactness assertion from the two preprints is
used here, because their introductory descriptions of the model system's
exactness are not consistent with one another.
