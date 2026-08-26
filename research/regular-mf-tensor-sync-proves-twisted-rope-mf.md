---
rg: 2
id: regular-mf-tensor-sync-proves-twisted-rope-mf
kind: claim
title: Relative finite edge models tensor with a regular-MF base to make the twisted rope MF
artifacts:
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
distinct_from:
  profinite-synchronized-hnn-is-regular-mf: that requires a cofinal synchronized finite quotient family of the whole vertex group; this allows the finite edge models to ignore arbitrary base factors because a separate regular-MF representation supplies faithfulness.
  twisted-rope-edge-is-mf-under-relative-profinite-compatibility: that preserves Britton reduction in finite HNN quotients; this proves compatibility directly in a matrix corona by tensoring the common base representation.
---

Let `Gamma` be regularly operator-MF realized, let `Q` be residually finite
with a cofinal sequence `beta_n:Q->B_n`, let `S<=Gamma`, and let
`tau:S->Q` be a homomorphism.  Suppose that for each `n` there is a homomorphism
to a finite group

```text
lambda_n:Gamma->C_n,
ker(lambda_n|S) <= ker(beta_n tau).                           (RTS1)
```

Then the twisted rope HNN extension

```text
R=<Gamma times Q,u |
   u(s,1)u^-1=(s,tau(s)), s in S>                            (RTS2)
```

is regularly operator-MF realized, hence operator-MF.

The maps `lambda_n` need not separate `Gamma`, and `S` need not be closed in
the profinite topology of `Gamma`.  All faithfulness on the `Gamma` coordinate
comes from its regular-MF model; the finite maps are used only to conjugate
the two edge restrictions exactly.
