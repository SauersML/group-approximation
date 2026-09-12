---
rg: 2
id: laminar-finite-subgroup-defect-gives-kaplansky-failure
kind: route
title: A laminar finite-subgroup idempotent with zero K_0 class is a stable finiteness failure, hence a direct finiteness failure
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-units-have-laminar-finite-subgroup-defect
  - leavitt-stable-finiteness-equals-direct-finiteness
artifacts:
  - research/artifacts/finite-subgroup-combination-defects-2026-09-12.md
---

Let `P = d S^n` be the nonzero projective of the prerequisite, with `[P] = 0` in `K_0(S)`.

1. **A strict pair.**
   - A vanishing class gives `P (+) Q ~= Q` for some finitely generated projective `Q`. Adding a
     complement of `Q` in a free module gives `P (+) S^m ~= S^m`.
   - Let `phi : S^m -> P (+) S^m` be such an isomorphism, `iota` the inclusion of the second
     summand, and `pi` its projection.
   - Put `a = phi^(-1) iota` and `c = pi phi`. Then `c a = pi iota = I_m`.
   - `a c` is the idempotent with kernel `phi^(-1)(P) != 0`, so `a c != I_m`.
2. **Down to scalars.** `M_m(S)` is not directly finite, so `S` is not stably finite.
   `leavitt-stable-finiteness-equals-direct-finiteness` then gives the scalar failure
   `leavitt-unit-group-algebra-not-directly-finite`.

This route is live, not dead. Its prerequisite is open, and the obstruction
`sofic-amalgam-finite-subgroup-idempotent-traces-are-strict` excludes only configurations with a
sofic intersection amalgam.
