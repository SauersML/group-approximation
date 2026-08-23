---
rg: 2
id: atlas-authenticated-s3-extension-minor-decodes-pairings
kind: claim
title: The authenticated S3 extension-channel rows have nuisance-quotient rank three on the Leavitt pairing monomials
distinct_from:
  atlas-hard-packet-authenticates-s4-extension-triple: that constructs the common three-coordinate channel and ties it to literal words; this is the remaining exact rank calculation after authentication.
  s3-hard-cell-three-channel-data-is-nondegenerate: that proves three candidate finite transforms are invertible abstractly; this asks whether the actual projected atlas relators contain one of those transforms on the desired path monomials.
  atlas-hard-packet-s3-channel-decoder: that is the combined dimension-free decoder theorem; this isolates its finite coefficient-rank half.
  separated-channel-identities-retain-rectangular-escape: that rules out applying a carrier determinant and coefficient equivariance in separate tensor factors; this demands a minor from genuinely mixed quotient-relator rows.
  atlas-mixed-minor-needs-nuisance-quotient-rank: that proves the exact amplification-uniform rank criterion; this asks the literal Atlas row census to satisfy it.
---

OPEN.  Assume the common extension-labelled channel from
`atlas-hard-packet-authenticates-s4-extension-triple`.  Inventory every named
hard, interior, and comb-constraining relator row on that channel.  For each
row record its word provenance, bracketing, input channels, output channel,
reduced multiplicity monomial, and exact coefficient in `Q(sqrt(2))`.

After eliminating monomials fixed by the exact packet laws, write the full
coefficient matrix as `[C D]`, where the three columns of `C` are precisely
the path products giving

```text
R0^* W L0-W,     R1^* W L1-W,     R0^* W L1.          (S3M1)
```

and `D` contains **every** other reduced multiplicity monomial occurring in
the same rows.  Prove the nuisance-quotient rank condition

```text
rank [C D]=rank D+3.                                  (S3M2)
```

By `atlas-mixed-minor-needs-nuisance-quotient-rank`, `(S3M2)` is exactly the
condition giving a fixed scalar left inverse which annihilates `D`.  Its
norm is a fixed algebraic constant, so the resulting coefficient-to-HS-
defect estimate is independent of external multiplicity.  A nonzero minor
of `C` without `(S3M2)` does not suffice: nuisance monomials can cancel all
three desired coordinates exactly at every amplification.
Every selected row must be a projection of an actual quotient relator in
which its finite carrier coefficient and multiplicity path-product occur in
the same term.  A scalar carrier matrix tensored with an independent
coefficient equation is inadmissible by the separated rectangular no-go.

## Attempts

- The stored `atlas-boundary-11-30.json` records only the two boundary words
  and their factor projections.  It contains neither the full interior/comb
  projected row census nor the reduced multiplicity monomial columns.  It
  therefore cannot decide `(S3M2)`.  Producing that typed census is the next
  finite computation; taking a determinant of the existing two-row artifact
  would not test this claim.
- Test first for the `F_sigma`, full restriction matrix, and central-overlap
  patterns already computed in `s3-hard-cell-three-channel-data-is-nondegenerate`.
  Their abstract determinants do not count unless every row has literal
  packet provenance.
- If other reduced multiplicity monomials enter the same rows, retain them as
  the nuisance matrix `D` and verify `(S3M2)`.  Computing a minor of `C` after
  merely deleting those columns would repeat the multiplicity-free-fusion
  error.
- Use the central projectors of the actual finite prefix group from
  `actual-hard-prefix-generates-s4-over-raw-s3`; no recovery from the
  classical fold remains necessary.  The rank calculation must nevertheless
  keep cross-products between the two extension decompositions as distinct
  operator variables until a relator identifies them.
- A complete row census with
  `rank[C D]-rank(D)<3` refutes this claim and therefore the present decoder
  route.  This is stronger than asking whether `rank(C)<3`.
