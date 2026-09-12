---
rg: 2
id: regular-mf-tensor-sync-proves-twisted-rope-mf
kind: claim
title: Relative finite edge models tensor with a regular-MF base to make the twisted rope MF
artifacts:
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
  - research/artifacts/regular-mf-tensor-sync-shulman-completion-2026-08-26.md
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
distinct_from:
  profinite-synchronized-hnn-is-regular-mf: that requires a cofinal synchronized finite quotient family of the whole vertex group; this allows the finite edge models to ignore arbitrary base factors because a separate regular-MF representation supplies faithfulness.
  twisted-rope-edge-is-mf-under-relative-profinite-compatibility: that preserves Britton reduction in finite HNN quotients; this proves compatibility directly in a matrix corona by tensoring the common base representation.
---

Let `Gamma` be countable and regularly operator-MF realized, let `Q` be
countable and residually finite
with an eventually separating cofinal sequence `beta_n:Q->B_n`, let
`S<=Gamma`, and let
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

The last implication uses Shulman's arXiv:2603.13564v2, body Theorem 16, after
Ueda's universal-HNN corner construction. Tensor synchronization supplies
faithful edge-compatible embeddings of both corner-amalgam vertices. Theorem
16 makes the universal HNN algebra MF; the particular finite edge intertwiner
alone need not give a faithful representation of the stable letter.
Equivalently, apply [[twisted-hnn-mf-permanence-with-corona-conjugator]] via
the independently checked route
[[regular-mf-tensor-sync-via-corona-conjugator]].

The maps `lambda_n` need not separate `Gamma`, and `S` need not be closed in
the profinite topology of `Gamma`.  All faithfulness on the `Gamma` coordinate
comes from its regular-MF model; the finite maps are used only to conjugate
the two edge restrictions exactly.  No trace-compatible matrix-corona model of
`Gamma` is assumed: the proof first works in an `A`-valued reduced product and
only then embeds its generated separable MF algebra into a matrix corona.

The final MF implication is not a claim that an arbitrary compatible finite
intertwiner separates Britton words.  It uses Shulman's
arXiv:2603.13564v2, Theorem 16, after Ueda's matrix-corner realization: the
two corner factors have faithful embeddings into the same matrix corona and
agree exactly on the amalgam.  Group injectivity and the regular character
then follow directly by mapping the universal HNN algebra to the left regular
representation of the abstract group HNN.
