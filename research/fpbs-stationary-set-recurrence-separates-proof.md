---
rg: 2
id: fpbs-stationary-set-recurrence-separates-proof
kind: route
title: Poincaré recurrence of the environment seen from the walker, and the zero-or-infinite lemma for aperiodic pmp relations
target: fpbs-stationary-set-recurrence-separates
requires: []
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

Complete proof in Sections 2--3 of the artifact. Imported only as standard
theorems: the Poincaré recurrence theorem, the Feldman--Moore theorem, and the
existence of a Borel linear order on a standard Borel space.

1. **(W).** `T(omega, xi) = (xi_1^{-1} omega, theta xi)` preserves
   `P ⊗ mu^{⊗N}` because `P` is invariant, and `T^n = (X_n^{-1} omega, ...)`.
   Let `B = {unique infinite cluster, and it contains e}`. Then
   `T^n z in B` iff `X_n in C_inf`. Poincaré recurrence gives infinitely many
   returns, and uniqueness gives `C_inf = C_e`.
2. **Lemma.** In an aperiodic pmp countable Borel relation, the set of points
   of `B` whose class meets `B` finitely is null. Pick the minimal point
   `F_0` of each such finite set. The `n`-th-point maps `phi_n` then give
   infinitely many disjoint copies of `F_0` of equal measure.
3. **(R).** Lift `R'` to `R~` on `Omega x Y` through the free diagonal action.
   The class of `(omega,y)` meets `B` exactly at `g^{-1}(omega,y)` with
   `g in A(y) ∩ C_inf(omega)`, so the Lemma applies.
4. **Corollary.** By monotonicity, finiteness at `p` holds at every `p' <= p`.
   A uniqueness parameter `p'` would have `theta(p') > 0` and contradict the
   theorem. So `p_u >= p`.
