---
rg: 2
id: projective-unitary-iac-misses-canonical-hyperlinear-embeddings
kind: claim
title: Polish-SIN automatic continuity cannot constrain a canonical hyperlinear embedding of a full projective unitary group
distinct_from:
  elementary-bcs-canonical-unitary-compiler-fence: that blocks a canonical elementary-matrix representation and asks for an abstract character theorem; this audits the tempting full-unitary-group automatic-continuity replacement.
  cdi-input-projective-word-law-remains-a-group-factor-gate: that characterizes projective word bases inside a tracial factor; this explains why continuity of the full projective unitary group cannot be invoked on the canonical discrete character.
  finite-support-corner-localizes-obstruction: that would finish after an algebraic corner map; this rules out obtaining such a map merely by applying Polish automatic continuity to an abstract hyperlinear embedding.
---

**ESTABLISHED SCOPE FIREWALL.**  Let `M` be a separable `II_1` factor.
Dowerk--Thom prove that every homomorphism

```text
PU(M) -> H                                                (PUA1)
```

is continuous when `H` is a **Polish SIN group** (arXiv:1506.08549,
Theorem 1.2 and its invariant automatic-continuity application).  This does
not turn hyperlinearity of the abstract discrete group `PU(M)` into a
trace-preserving embedding of `M`.

Indeed, a canonical-character hyperlinear embedding sends any two distinct
group elements to normalized-HS distance `sqrt(2)`.  Its image is therefore
discrete.  Since `PU(M)` is uncountable, that image is nonseparable, and the
matrix ultraproduct containing it is not a Polish target on this image.  The
separability hypothesis in `(PUA1)` cannot be recovered by taking the closure
of the image.

This boundary is logically sharp.  Give the same abstract group `PU(M)` the
discrete metric.  It is a complete bi-invariant metric group, and the identity
homomorphism from the usual Polish `PU(M)` to this nonseparable SIN group is
discontinuous.  Hence no extension of the cited theorem to arbitrary complete
SIN targets is possible.

Passing to a countable dense subgroup makes the target image separable but
removes the automatic-continuity theorem: the domain is then only an abstract
countable group and the canonical character deliberately equips it with the
discrete HS metric.  Thus the full-unitary-group route still needs new
algebraic relations forcing continuity or trace recovery; automatic
continuity alone does not promote the non-CE factor trace to a canonical group
trace.
