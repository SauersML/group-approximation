---
rg: 2
id: fixed-term-chain-defeats-bounded-syndrome-neighborhoods
kind: claim
title: A fixed qubit spin chain defeats every prescribed bounded-size bounded-occurrence syndrome neighborhood system
artifacts:
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
  - scripts/check_qpcp_chain_obstruction.py
  - research/artifacts/qpcp-fixed-term-chain-replay-2026-09-07.json
distinct_from:
  qubit-pairs-have-half-gap-and-unbounded-rounder-cost: that has constant combinatorial gap but varying local term matrices and finite diverging global cost; this fixes the local matrices and excludes every finite local charge constant for bounded neighborhoods, but has vanishing combinatorial gap.
  amplifier-admits-a-uniform-local-kernel-resolution: that asks for a construction on special amplified NO outputs; this refutes only the generic inference from finite local term types and local spectra, using an explicit family outside the constant-combinatorial-gap premise.
---

Let `K_n=|1><1|_1+sum_i (I-SWAP_(i,i+1))/2+|0><0|_n`, for `n>=2`.
It is frustrated, uses a fixed finite collection of norm-one qubit
projectors of locality two and degree two, and has minimum exact fault
cardinality one. It has a rational product state of total energy at most
`2/(n-1)`.

For any fixed integers `L,R>=1` and `n>1+16R(L+1)^4`, every system of
energy neighborhoods of cardinality at most `L` and occurrence at most `R`
fails to support an exactifying instrument with `F_a<=C_0 A_a` for any
finite `C_0`. Each local sum nevertheless has positive spectrum at least
`1/[8(L+1)^4]`. This excludes an unconditional local-spectra-to-resolution
inference, not a constant-combinatorial-gap amplifier or quantum PCP.

Equivalently, any finite-cost local construction on this unmodified chain
must have `R(L+1)^4 >= (n-1)/16`. This is a necessary resource bound, not a
sufficiency theorem at the threshold.
