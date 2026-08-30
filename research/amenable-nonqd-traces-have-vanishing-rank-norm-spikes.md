---
rg: 2
id: amenable-nonqd-traces-have-vanishing-rank-norm-spikes
kind: claim
title: Amenable nonquasidiagonal traces force operator-norm spikes on vanishing-rank corners
distinct_from:
  stw99-problem-x1-fails-on-full-group-algebras: that supplies existence of an amenable non-QD trace; this is the finite-dimensional geometry of every u.c.p. amenability sequence for any such trace.
  literal-folner-ucp-models-have-sharp-norm-hs-separation: that computes one explicit rank-one boundary; this gives a nonconstructive fixed pair for an arbitrary amenability sequence and quantitative spectral-tail and dimension-growth estimates.
artifacts:
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

Let `A` be separable and unital, let `tau` be an amenable trace which is
not quasidiagonal, and let

```text
Phi_n:A -> M_(d_n)
```

be any u.c.p. sequence witnessing amenability: normalized traces converge to
`tau` and every multiplication defect tends to zero in normalized
Hilbert--Schmidt norm.  Then there are contractions `a,b in A`, a number
`eta>0`, and a subsequence such that, for

```text
D_n=Phi_n(ab)-Phi_n(a)Phi_n(b),
P_n=1_[eta/2,infinity)(|D_n|),
```

one has

```text
||D_n|| >= eta,                       P_n != 0,
tr_(d_n)(P_n) <= 4 ||D_n||_2^2 / eta^2 -> 0,
d_n >= eta^2 / ||D_n||_2^2 -> infinity.
```

Thus failure of quasidiagonality in an amenability model is necessarily an
operator-norm spike on asymptotically trace-zero singular directions.  The
matrix size must grow at least at the inverse square of the Hilbert--Schmidt
multiplication error of the obstructing pair.
