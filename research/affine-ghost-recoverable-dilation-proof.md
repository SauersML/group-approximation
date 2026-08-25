---
rg: 2
id: affine-ghost-recoverable-dilation-proof
kind: route
title: Commute affine hull with the decoder and audit the trace operations
target: affine-ghosts-survive-recoverable-tracial-dilations
requires:
  - agent-free-compressor-reynolds-zero-has-affine-ghosts
  - tracial-cap-menus-are-central-core-partitions
  - locally-affine-support-bcs-is-exactly-the-lcs-boundary
---

Affine maps commute with affine hull:

```text
pi(Aff(S_tilde))=Aff(pi(S_tilde))=Aff(S).              (AGD4)
```

If the left hull is contained in `R_tilde`, `(AGD1)` and `(AGD4)` give

```text
Aff(S) subseteq pi(R_tilde) subseteq R,
```

which proves `(AGD2)`.  For a direct sum, every summand support is contained
in the union support, so monotonicity of affine hull gives item 2.  The
decoders in items 1, 3, and 4 are the displayed identity, marginal, and
`(u,t) |-> u+t` maps.

Finally, the exact-compression part of
`tracial-cap-menus-are-central-core-partitions` says that a compression of a
faithful normal trace is tracial on the generated algebra only on a central
carrier.  This proves the postselection assertion and completes the audit.

