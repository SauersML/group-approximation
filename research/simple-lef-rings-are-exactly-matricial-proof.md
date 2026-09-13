---
rg: 2
id: simple-lef-rings-are-exactly-matricial-proof
kind: route
title: Project each finite model onto a simple factor of its semisimple quotient, then use simplicity for injectivity
target: simple-lef-rings-are-exactly-matricial
requires: []
artifacts:
  - research/artifacts/un-lef-converse-2026-09-13-part1.md
---

1. Let `W_1 ⊆ W_2 ⊆ ...` exhaust `R`, with injective partial ring homomorphisms `phi_n : W_n -> Q_n` into
   finite unital rings, preserving `0`, `1`, and the sums and products inside `W_n`. `Q_n != 0`, since
   `phi_n(0) != phi_n(1)`.
2. `J(Q_n)` is the Jacobson radical. By Artin–Wedderburn and Wedderburn's little theorem, `Q_n / J(Q_n)` is a
   nonzero finite product of matrix rings `M_d(F_q)`. Let `p_n` be the unital surjection onto one factor
   `M_(d_n)(F_(q_n))`, and `psi_n = p_n ∘ phi_n`. Then `psi_n` is unital and preserves the sums and products in
   `W_n`; it need not be injective.
3. Define `Psi(r) = [psi_n(r)]_omega`, well defined because `r ∈ W_n` for all large `n`. `Psi` is a unital ring
   homomorphism.
4. `Psi(1) = 1 != 0`, as `d_n >= 1`. So `ker Psi` is a proper two-sided ideal, hence `0` by simplicity. ∎

Recalled, not re-derived: Artin–Wedderburn and Wedderburn's little theorem (finite division rings are fields).
