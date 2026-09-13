---
rg: 2
id: pumped-divergent-minsky-word-lies-in-profinite-kernel-proof
kind: route
title: Clock invariant for non-acceptance, idempotent operator powers for the finite quotients
target: pumped-divergent-minsky-word-lies-in-profinite-kernel
requires:
  - kms-minsky-machine-groups-simulate-their-machines
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md
---

The full proof is Lemma A (Section 3) of
`research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md`.

**Step 1.**  The pumped input `c' = (c; 1, 0)` is not accepted by `P(M)`.

- Every command preserves `iota = e_pi - e_rho - e_tau`, and `iota(c') = 1`.
  A drain needs `e_pi = e_rho = 0`, which forces `iota = -e_tau <= 0`.
- Reaching command `0` through a command of `M` projects to a computation of
  `Sym(M)` from `c` to a stop configuration.  By Lemma 2.1 (determinism) the
  stop configuration would lie on the forward orbit of `c`, which diverges.

So the semigroup word of `c'` is nonzero, and by the simulation theorem
(clause 4 of the import) `w(c') != w(0; 0..0)` in `G(P(M))`.

**Step 2.**  Fix a finite quotient `phi` and put `V = phi(T)`.

1. `f |-> f * a_pi` is a product of conjugates.  It therefore induces an
   endomorphism `P̄` of `V`, and some `P̄^D` is idempotent, so
   `P̄^m = P̄^(m+tD)` for `m >= D`.
2. Along the lifted divergent computation `e_rho = 0`, and `e_pi` increases by
   one at every Add, taking every value `>= 1`.  Choose a configuration `d`
   with `e_pi(d) = tD`.
3. Pump `D` times.  Under `phi`, the block `(*a_pi)^(tD+D)` of the
   configuration word collapses to `P̄^D`, so `phi(w(d; tD+D, D)) =
   phi(w(d; D, D))`.
4. Unpump to `(d; 0, 0)`; the drain reaches command `0`, whose word is `0` in
   the semigroup.

By clause 4 each semigroup equality is a group equality.  Chaining gives
`phi(w(c')) = phi(w(0; 0..0))`.
