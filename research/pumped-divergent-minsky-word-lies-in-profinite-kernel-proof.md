---
rg: 2
id: pumped-divergent-minsky-word-lies-in-profinite-kernel-proof
kind: route
title: Clock invariant for non-acceptance, idempotent operator powers for the finite quotients
target: pumped-divergent-minsky-word-lies-in-profinite-kernel
requires:
  - kms-minsky-machine-groups-simulate-their-machines
  - kms-group-with-stop-relations-simulates-all-words
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md
---

The full proof is Lemma A (Section 3) of
`research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md`.  The group is
`G_0(P(M))`, the KMS group with the stop relations `x_(q_0 w) = 1`.  Clause 2
of [[kms-group-with-stop-relations-simulates-all-words]] plays the role of the
simulation theorem, zero words included.

**Step 1.**  The pumped input `c' = (c; 1 + e_tau(c), 0)` is not accepted by
`P(M)`.

- Every command preserves `iota = e_pi - e_rho - e_tau`, and `iota(c') = 1`.
  A drain needs `e_pi = e_rho = 0`, which forces `iota = -e_tau <= 0`.
- Reaching command `0` through a command of `M` projects to a computation of
  `Sym(M)` from `c` to a stop configuration.  By Lemma 2.1 (determinism) the
  stop configuration would lie on the forward orbit of `c`, which diverges.

So the semigroup word of `c'` is nonzero.  By clause 2 of the stop-relation
claim, `w(c') != w(0; 0..0) = 1` in `G_0(P(M))`.

**Step 2.**  Fix a finite quotient `phi` and put `V = phi(T)`.

1. `f |-> f * a_pi` is a product of conjugates.  It therefore induces an
   endomorphism `P̄` of `V`, and some `P̄^D` is idempotent, so
   `P̄^m = P̄^(m+tD)` for `m >= D`.
2. Along the lifted divergent computation `e_rho = 0` and
   `e_pi = 1 + e_tau`, which increases by one at every Add and takes every
   value `>= 1 + e_tau(c)`.  Choose a configuration `d` with `e_pi(d) = tD`.
3. Pump `D` times.  Under `phi`, the block `(*a_pi)^(tD+D)` of the
   configuration word collapses to `P̄^D`, so `phi(w(d; tD+D, D)) =
   phi(w(d; D, D))`.
4. Unpump to `(d; 0, 0)`; the drain reaches command `0`, whose word is `0` in
   the semigroup.

By clause 2 of the stop-relation claim, each semigroup equality is a group
equality in `G_0(P(M))`, and the zero word at the end is `1`.  Chaining gives
`phi(w(c')) = 1 = phi(w(0; 0..0))`.

(Corrected after review by `ex-verify-groups`: the earlier input `(c; 1, 0)`
has invariant `1 - e_tau(c)`, not `1`.)

(Corrected after review by `ex-verify-logic-quantum`.  The last step ends at a
`phi`-dependent stop configuration, and under KMS's displayed relations the
words of distinct stop configurations are distinct.  The stop relations make
them all `1`.  See `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md`
§1.4.)
