---
rg: 2
id: correctable-data-tests-are-logically-blind
kind: claim
title: A test confined to an erasure-correctable data region and arbitrary auxiliary proof cannot read the logical state on the exact code space
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/qpcp-integration-ledger-2026-09-20.md
distinct_from:
  factorwise-complete-composition-returns-the-input-energy: that constructs low-energy states for independently encoded bits and clause-private proofs; this permits an arbitrary correlated code and shared auxiliary proof but assumes each test reads an erasure-correctable data region on a fixed exact code space.
  tracial-internality-does-not-supply-local-witness-control: that distinguishes trace and abstract algebra from witness control; this derives a separate restriction from exact quantum error correction.
---

Let `E:K_logical -> K_data` be an isometric encoding. Suppose every data
region touched by a test is erasure-correctable by this exact code. For any
test `g` on one such region and an arbitrary auxiliary register `A`, there
is an operator `B_g` on `A` such that

```text
(E* tensor I_A) g (E tensor I_A) = I_logical tensor B_g.
```

If `g` is a positive contraction then so is `B_g`. Consequently every
state supported on the code, even entangled with `A`, has test energy
determined solely by its auxiliary marginal. Summing tests preserves this
conclusion even if their correctable data regions differ.

This constrains a fixed-code-space strategy for local logical verification.
It does not exclude a changing encoding, decoding, testing a larger region,
or another construction that supplies its own all-state energy proof.

The continuation distinguishes this full logical blindness from
[[distance-code-local-tests-are-label-diagonal]], which only removes
logical off-diagonal blocks for a classical Hamming-distance encoding.
Its diagonal blocks can still depend on the logical label and act
quantumly on a shared auxiliary register. That weaker conclusion has a
separate leakage estimate in [[distance-code-leakage-bounds-phase-energy]].
