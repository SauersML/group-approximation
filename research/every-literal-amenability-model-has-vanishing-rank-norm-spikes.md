---
rg: 2
id: every-literal-amenability-model-has-vanishing-rank-norm-spikes
kind: claim
title: Every amenability model of the literal canonical trace has vanishing-rank operator-norm spikes
distinct_from:
  literal-folner-ucp-models-have-sharp-norm-hs-separation: that gives the explicit stable-letter boundary in the constructed sequence; this quantifies over every u.c.p. sequence witnessing amenability, with the obstructing pair allowed to depend on the sequence.
  effective-transport-modulus: that asks for one effective relator-level threshold forcing the literal marked word close to one; this theorem gives an explicit rank inequality after a persistent norm defect has been selected, but does not compute the universal finite test or threshold.
artifacts:
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

**ESTABLISHED.**  Every u.c.p. matrix sequence witnessing amenability of the
canonical trace `tau_E` contains a fixed multiplication pair with
operator-norm defect bounded away from zero along a subsequence.  For a
threshold `eta>0`, the singular subspace above `eta/2` is nonzero but has
normalized dimension at most

```text
4 ||Phi_n(ab)-Phi_n(a)Phi_n(b)||_2^2 / eta^2,
```

and hence asymptotic normalized dimension zero.

Existence of amenability sequences is the literal factorization theorem.
Their norm defect cannot vanish on every pair because `tau_E` is not
quasidiagonal.  The general vanishing-rank spike theorem then gives the
quantitative conclusion.  In the concrete Folner sequence the pair can be
taken to be `(u,u*)`, the threshold can be any `eta<1`, and the spike is
exactly one endpoint block of normalized rank `1/N`.
