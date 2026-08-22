---
rg: 2
id: finite-window-decoder
kind: claim
title: Finite-window endomorphism decoder
artifacts:
  - notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md
  - notes/TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md
---

Extract from the joint outer characters common finite paired-radical label
spaces on which the four one-sided Leavitt maps act with vanishing boundary
and pairing error (AGENDA 2026-08-14, "one comb compressor gives one joint
outer PVM"). Caution: a common carrier alone is NOT a decoder — the finite
`UT₄(F₂)` regular model realizes the carrier and the full nested table
without one (carrier-not-decoder).

It is sufficient to decode the three products consumed by
leavitt-multiplicative-trace-floor on the canonical trace-`1/8` Pauli corner;
the additive Leavitt relation and an unspecified nonzero corner are not
needed.  The fixed density converts ambient microstate errors to normalized
corner errors with no vanishing-rank escape.

The concrete live decomposition is now
`finite-window-decoder-from-s3-hard-packet`: localize to the exact raw `S3`
packet, compile products into multiplicity-one channels, and ask whether the
literal full hard/comb system has a nonzero minor decoding the two diagonal
and one crossed pairing defects.  The exact finite transforms are established
in `s3-hard-cell-three-channel-data-is-nondegenerate`; the actual relator-rank
gate remains `atlas-hard-packet-s3-channel-decoder`.
