---
rg: 2
id: binary-counterexample-from-rank-kill-and-state-realization
kind: route
title: The Sylvester two-root gate plus state realization on the complement corner makes the binary cyclic corner full
target: binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
requires:
  - sylvester-rank-functions-on-leavitt-units-kill-two-root-defect
  - binary-complement-corner-rank-functions-pull-back-to-units
  - binary-complement-corner-states-give-sylvester-rank-functions
  - binary-cyclic-corner-full-iff-complement-corner-has-no-state
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

Artifact Corollary C.1. Let `T = (1 - e) F_2[R^x] (1 - e)`.

1. **The gate.** Every Sylvester rank function on `F_2[R^x]` kills the two-root defect, so it is the
   augmentation rank.
2. **Move to the corner.** By `binary-complement-corner-rank-functions-pull-back-to-units`, `T` carries no
   normalized Sylvester rank function.
3. **State realization.** By `binary-complement-corner-states-give-sylvester-rank-functions`,
   `(K_0(T), [T])` has no state.
4. **The corner.** By `binary-cyclic-corner-full-iff-complement-corner-has-no-state`, `c e b = 1` is
   solvable. The route `binary-cyclic-corner-fullness-gives-kaplansky-failure` then continues toward the goal.

**Payoff.** This is the characteristic-two counterpart of `ternary-counterexample-from-rank-kill-and-state-realization`.
Both premises are open. The first is the binary rank gate in Sylvester form. The second is ring theory with
no group input beyond the halving homomorphism.
