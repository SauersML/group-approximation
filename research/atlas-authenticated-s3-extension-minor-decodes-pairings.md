---
rg: 2
id: atlas-authenticated-s3-extension-minor-decodes-pairings
kind: claim
title: The authenticated S3 extension-channel rows have a nonzero minor on the three Leavitt pairing monomials
distinct_from:
  atlas-hard-packet-authenticates-s4-extension-triple: that constructs the common three-coordinate channel and ties it to literal words; this is the remaining exact rank calculation after authentication.
  s3-hard-cell-three-channel-data-is-nondegenerate: that proves three candidate finite transforms are invertible abstractly; this asks whether the actual projected atlas relators contain one of those transforms on the desired path monomials.
  atlas-hard-packet-s3-channel-decoder: that is the combined dimension-free decoder theorem; this isolates its finite coefficient-rank half.
---

OPEN.  Assume the common extension-labelled channel from
`atlas-hard-packet-authenticates-s4-extension-triple`.  Inventory every named
hard, interior, and comb-constraining relator row on that channel.  For each
row record its word provenance, bracketing, input channels, output channel,
reduced multiplicity monomial, and exact coefficient in `Q(sqrt(2))`.

After eliminating monomials fixed by the exact packet laws, the coefficient
matrix contains a nonzero minor whose three solved coordinates are precisely
the path products giving

```text
R0^* W L0-W,     R1^* W L1-W,     R0^* W L1.          (S3M1)
```

The inverse-minor norm is a fixed algebraic constant, so the resulting
coefficient-to-HS-defect estimate is independent of external multiplicity.

## Attempts

- Test first for the `F_sigma`, full restriction matrix, and central-overlap
  patterns already computed in `s3-hard-cell-three-channel-data-is-nondegenerate`.
  Their abstract determinants do not count unless every row has literal
  packet provenance.
- If other reduced multiplicity monomials enter the same rows, retain them as
  unknowns and compute rank after projection to the quotient by already
  authenticated packet identities.  Dropping them by hand would repeat the
  multiplicity-free-fusion error.
- A complete row census with rank below three on `(S3M1)` refutes this claim
  and therefore the present decoder route.
