---
rg: 2
id: pumped-divergent-minsky-word-lies-in-profinite-kernel
kind: claim
title: A divergent computation of a clocked machine becomes invisible to every finite quotient of the pumped machine group
distinct_from:
  kms-minsky-machine-groups-simulate-their-machines: that is the imported simulation theorem; this is a new non-residual-finiteness mechanism built on it, which KMS use only quantitatively (depth functions) and without the clock that makes the input non-accepted.
  pumped-halting-clocked-minsky-group-is-residually-finite: that is the positive half for universally halting machines; this is the negative half for machines with a divergent configuration.
---

ESTABLISHED.  The statement was corrected twice: on 2026-09-12 after review by
`ex-verify-groups`, and on 2026-09-13 after review by `ex-verify-logic-quantum`.

Let `M` be a deterministic Minsky machine clocked by a glass `tau`:

- no command subtracts from or tests `tau`;
- every Add adds a coin to `tau`;
- every Sub or zero test is followed by a pure `Add(tau)` command.

Let `P(M)` add two glasses `pi, rho`, with these commands:

- every Add of `M` also adds a coin to `pi`;
- at each nonzero command number `i`, a pump `i -> Add(pi, rho); i`;
- at each nonzero command number `i`, a drain `i; e_pi = 0, e_rho = 0 -> 0`.

Let `G_0(P(M))` be the KMS group of `P(M)` with the stop relations
`x_(q_0 w) = 1` added ([[kms-group-with-stop-relations-simulates-all-words]]).
In it `w(0; 0...0) = 1`.

Suppose some configuration `c` of `M` has an infinite forward computation, and
put `c' = (c; pi = 1 + e_tau(c), rho = 0)`.  Then in the finitely presented
group `G_0(P(M))`,

```text
w(c') != w(0; 0...0),
phi(w(c')) = phi(w(0; 0...0))   for every finite quotient phi,
```

so `G_0(P(M))` is not residually finite.

Two ingredients:

- *Non-acceptance.*  `iota = e_pi - e_rho - e_tau` is invariant under every
  command, and `iota(c') = 1`.  A drain would need `iota = -e_tau <= 0`.
  Lemma 2.1 excludes reaching stop through `M`.
- *Finite quotients.*  The operator `*a_pi` induces an endomorphism of the
  finite group `phi(T)`, some power `P̄^D` of which is idempotent.  Run the
  divergent computation until `e_pi = tD`, pump `D` times, replace `P̄^(tD+D)`
  by `P̄^D`, unpump to `(0,0)`, and drain.

**Correction.**  An earlier version used `c' = (c; 1, 0)`.  Its invariant is
`1 - e_tau(c)`, and the statement fails when `c` is reached from a clock-zero
configuration by an Add: run that Add backward, then drain.
[[rf-fp-completeness-via-pumped-minsky-groups]] is unaffected, because its
divergent configuration has `e_tau = 0`.

**Correction (stop relations).**
- **Where the gap is.**  The drain in Step 2 reaches a stop configuration
  `(0; e(d), 0, 0)`.  The configuration `d` depends on the idempotent exponent `D`, hence on
  `phi`.
- **What the step needs.**  Identifying the stop word with `w(0; 0...0)` for every `phi` needs
  every zero semigroup word to be trivial.  This is clause 2 of
  [[kms-group-with-stop-relations-simulates-all-words]].
- **Why `G(P(M))` does not give it.**  The clause fails for `G(P(M))` under KMS's displayed
  relations G1--G8, where distinct stop configurations have distinct words.
- **The fix.**  The statement is now made for `G_0(P(M))`.  In part 1 of the artifact, read
  `G_0` for `G`.
- **Review.**  `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md` §1.4.

DERIVATION
[[pumped-divergent-minsky-word-lies-in-profinite-kernel-proof]]
