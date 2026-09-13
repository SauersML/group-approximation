---
rg: 2
id: pumped-divergent-minsky-word-lies-in-profinite-kernel
kind: claim
title: A divergent computation of a clocked machine becomes invisible to every finite quotient of the pumped machine group
distinct_from:
  kms-minsky-machine-groups-simulate-their-machines: that is the imported simulation theorem; this is a new non-residual-finiteness mechanism built on it, which KMS use only quantitatively (depth functions) and without the clock that makes the input non-accepted.
  pumped-halting-clocked-minsky-group-is-residually-finite: that is the positive half for universally halting machines; this is the negative half for machines with a divergent configuration.
---

ESTABLISHED (unreviewed).  Let `M` be a deterministic Minsky machine clocked
by a glass `tau`:

- no command subtracts from or tests `tau`;
- every Add adds a coin to `tau`;
- every Sub or zero test is followed by a pure `Add(tau)` command.

Let `P(M)` add two glasses `pi, rho`, with these commands:

- every Add of `M` also adds a coin to `pi`;
- at each nonzero command number `i`, a pump `i -> Add(pi, rho); i`;
- at each nonzero command number `i`, a drain `i; e_pi = 0, e_rho = 0 -> 0`.

If some configuration `c` of `M` has an infinite forward computation, then in
the finitely presented group `G(P(M))`,

```text
w(c; pi=1, rho=0) != w(0; 0...0),
phi(w(c; pi=1, rho=0)) = phi(w(0; 0...0))   for every finite quotient phi,
```

so `G(P(M))` is not residually finite.

Two ingredients:

- *Non-acceptance.*  `iota = e_pi - e_rho - e_tau` is invariant under every
  command, so a drain never applies from this input.  Lemma 2.1 excludes
  reaching stop through `M`.
- *Finite quotients.*  The operator `*a_pi` induces an endomorphism of the
  finite group `phi(T)`, some power `P̄^D` of which is idempotent.  Run the
  divergent computation until `e_pi = tD`, pump `D` times, replace `P̄^(tD+D)`
  by `P̄^D`, unpump to `(0,0)`, and drain.

DERIVATION
[[pumped-divergent-minsky-word-lies-in-profinite-kernel-proof]]
