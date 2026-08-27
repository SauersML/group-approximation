---
rg: 2
id: regular-tensor-camouflage-preserves-moving-root-failures
kind: claim
title: Regular tensor camouflage preserves conductor-moving root geometry
distinct_from:
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that preserves edge defects and projection commutators abstractly; this shows explicitly how moving root polynomials recover the payload through the regular tensor factor.
  canonical-trace-does-not-control-moving-root-orthogonality: that gives a standalone clock example; this embeds the same quantifier failure into the exact residual-finite camouflage used by the Iwahori regular branch.
  opposite-root-orthogonality-charges-two-jump-gauges: that proves orthogonality inside a pure left regular quotient packet; this explains why tensoring such a packet onto arbitrary payload does not impose that orthogonality on conductor-moving coefficients.
---

Use the notation of
`residual-finite-tensor-camouflages-iwahori-transfer-failures`.  Let
`lambda_n` be the left regular representation of a finite quotient `Q_n`
and let `N_n` be the order of the image of the upper root element `u`.
For the amplified upper root

```text
U'_n=pi_(n,+)(u) tensor lambda_n(u)
```

one has the exact identity

```text
(U'_n)^(N_n)=pi_(n,+)(u)^(N_n) tensor 1.              (RTM1)
```

The analogous identity holds for the opposite root (using its order in
`Q_n`).  Therefore conductor-dependent polynomials in the amplified root
unitaries contain payload-only operators.  For such operators every mixed
normalized-HS product and commutator norm is exactly the original payload
norm, because tensoring with `1` is an isometry.

At the same time the amplified pair has the same Iwahori edge defect and
every fixed amalgam word has asymptotically canonical trace.  Consequently
any moving-coefficient failure of opposite-root multiplication isometry in
a candidate edge-compatible payload survives regular tensor camouflage.

This is a conditional preservation theorem, not a construction of a failed
Iwahori sequence.  Its consequence is logical but load-bearing: canonical
regular localization plus edge compatibility cannot by itself prove the
moving-coefficient tensor isometry needed to globalize
`opposite-root-orthogonality-charges-two-jump-gauges`.  Such a proof must use
the full cubic/Weyl relations to repair or split the payload geometry; if it
assumes the moving isometry after camouflage, it has assumed away the same
relative exactification problem.

