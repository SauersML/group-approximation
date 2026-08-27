---
rg: 2
id: dfnqxy-mie-pcpp-provenance-and-linear-no-go-proof
kind: route
title: Trace the Mie parameter block and xor three Hadamard codewords
target: dfnqxy-mie-pcpp-has-no-global-affine-replacement
requires:
  - dfnqxy-pcpp-contract-allows-nonlinear-proof-views
  - hadamard-pcpp-reflects-affine-unsafety
---

Read the four primary sources named in the claim.  The exact randomness,
query, and verification-time block in DFNQXY is Natarajan--Wright's quoted
form of Mie's Theorem 1; Fu--Mastel--Zhang explicitly identifies Mie and
records the circuit-table/oracularization/gap-amplification/alphabet-
reduction construction.  Natarajan--Vidick state the linear-proof property
only for an AND of linear constraints, not for an arbitrary `L_Enc`.

For the no-go, use the valid pairs `(e_i,e_i)`, `i=1,2,3`.  Affine proof
encoding, coordinate restriction, and affine local checks preserve their
odd xor for every random seed.  The xor is the pair of Hadamard encodings of
`111`, at relative distance `1/2` from the three-word language, contradicting
PCPP soundness for `gamma<=1/4` and `s<1`.
