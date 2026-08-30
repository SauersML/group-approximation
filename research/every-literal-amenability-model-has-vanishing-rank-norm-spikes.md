---
rg: 2
id: every-literal-amenability-model-has-vanishing-rank-norm-spikes
kind: claim
title: Every amenability model of the literal canonical trace has vanishing-rank operator-norm spikes
distinct_from:
  literal-folner-ucp-models-have-sharp-norm-hs-separation: that gives the explicit stable-letter boundary in the constructed sequence; this quantifies over every u.c.p. sequence witnessing amenability, with the obstructing pair allowed to depend on the sequence.
  effective-transport-modulus: that asks for one effective relator-level threshold forcing the literal marked word close to one; this theorem gives explicit spectral-rank and dimension inequalities after a persistent norm defect has been selected, but does not compute the universal finite test or threshold.
artifacts:
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

**ESTABLISHED.**  Every u.c.p. matrix sequence witnessing amenability of the
canonical trace `tau_E` contains a fixed multiplication pair with
operator-norm defect bounded below by some `eta>0` along a subsequence.  If

```text
D_n=Phi_n(ab)-Phi_n(a)Phi_n(b),
P_n=1_[eta/2,infinity)(|D_n|),
```

then

```text
P_n != 0,
tr(P_n) <= 4 ||D_n||_2^2/eta^2 -> 0,
d_n >= eta^2/||D_n||_2^2 -> infinity.
```

Existence of amenability sequences is the literal factorization theorem.
Their norm defect cannot vanish on every pair because `tau_E` is not
quasidiagonal.  The general vanishing-rank spike theorem gives the quantitative
conclusion.

For the concrete Folner sequence the pair is `(u,u*)`, one may take
`eta=1`, and the defect is exactly one endpoint block: operator norm `1`,
normalized Hilbert--Schmidt square `1/N`, normalized rank `1/N`, and target
dimension `d=N|Q|`.  Hence the universal dimension inequality reads
`N|Q| >= N`, with equality precisely when the residual packet has
`|Q|=1`.
