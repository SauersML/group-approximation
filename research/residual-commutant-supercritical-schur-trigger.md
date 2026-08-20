---
rg: 2
id: residual-commutant-supercritical-schur-trigger
kind: claim
title: A finite self-detecting compressor activates supercritical Schur cells in the residual commutant
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  matrix-recovery-of-schur-flip-wreath-sites: that asks to recover more than the logarithm of the entire current multiplicity in one coordinate theorem; this allows any already recovered cells to be factored off and asks the adaptive trigger to outrun only the residual spectator.
  compressor-amplifies-schur-flip-cocycle-rank: that is the resulting total-rank amplifier; this is the narrower dimension-diagonal operation inside the commutant left after exact old cells.
---

Construct a finite group-word compressor with the following normalized-HS
microstate property.  After any finite family of recovered forbidden Schur
flip cells has exactified on a positive-density packet carrier, use `(RMT1)`
to write its external multiplicity as

```text
C^(2^n) tensor C^L.
```

Either the named relator energy already exceeds a universal constant, or the
compressor, inside the residual commutant `M_L(C)`, activates `r` additional
independent flip cells satisfying

```text
r > log_2 L.                                                      (RST1)
```

The new cells must exactify on a subcarrier losing at most `C E_rel` mass,
retain the central sign, and return to the original packet carrier with total
squared HS loss at most `C E_rel`, where `C` is independent of `L`, `r`, and
the computation time used to choose them.  Loss of the carrier or escape from
the old-cell commutant must pay the same fixed energy floor.

By `(RMT2)`, the low-energy branch of `(RST1)` would imply simultaneously
`2^r|L` and `2^r>L`, a contradiction.  The selection of `r` must be
made from finite-multiplicity data of the same microstate; an externally fixed
sequence of larger windows is ruled out by
`infinite-index-does-not-force-supercritical-site-rank`.

This is the final dimension-diagonal hardware in residual form.  Polynomial
identities of `M_L(C)` or a recursively compressed constant-gap verifier are
candidate sensors, but direct evaluation of a degree depending on `L` cannot
be charged by word telescoping with a universal constant.

## Attempts

- Recovering every externally fixed finite site window fails by arbitrary
  spectator amplification `L`.
- A polynomial identity can detect `L` exactly in `M_L(C)`, but its degree and
  coefficient mass grow with `L`; direct word evaluation loses the required
  uniform HS constant.
- The live attack is to feed that endogenous stopping event into a recursively
  compressed constant-gap verifier and make its output select new wreath
  sites in the residual commutant.  The missing point is finite group-word
  semantic transport with cost independent of verifier runtime and output
  length.  The exact stopping program and its remaining groupification are now
  isolated by `schur-residual-commutant-is-a-dimension-oracle-tape` and
  `constant-hs-groupification-of-residual-dimension-tape`.
- A bounded group-native formulation avoids additive polynomial evaluation:
  `schur-flip-rank-is-residual-atomic-granularity` identifies the target as
  splitting below the smallest nonzero trace `1/L` in the residual matrix
  factor.  Its direct compiler is
  `constant-hs-groupification-of-residual-dyadic-splitter`; recursive
  constant-gap control, not the local Pauli actuator, remains open.
