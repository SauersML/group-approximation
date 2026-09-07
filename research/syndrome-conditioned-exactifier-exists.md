---
rg: 2
id: syndrome-conditioned-exactifier-exists
kind: claim
title: Conditioned on the measured syndrome set, a channel returns a state exact off that set
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
---

Hypothesis (EX) of `commuting-syndrome-domination-gives-a-rounder`, for the
amplified Hamiltonian.  After the joint measurement of the commuting ports
`B_j` of `local-syndrome-port-domination-at-each-gadget`, with
`S = {a : B_a reads 1}`, there is a CPTP map returning a normalized state on
the space where the `h'_a` act, satisfying

```text
h'_a sigma_S = 0   for every a not in S.                        (EXA1)
```

Two clauses that are easy to lose.

- **The output lives on `H`, not on `H_data`.**  Clause (1) of the rounder
  definition tests `sigma_S` against `h'_a`, so the pullback along `W` is
  part of the hypothesis.  A construction which exactifies "the data
  register" has not discharged this until the pullback is exhibited.
- **Exactness, not closeness.**  `Tr(h'_a sigma_S) = 0` is equivalent to
  `h'_a sigma_S = 0` for positive `h'_a`, and no approximate version of it
  suffices: the transfer theorem consumes exact satisfaction pointwise on
  every measurement outcome.

## Attempts

**Exact criterion for a fixed candidate.** Put `E_S = W^* Pi_S W`, where
`Pi_S` is the joint syndrome projector for the same `W,B` used in the local
cost estimate. By `joint-syndrome-support-characterizes-exactifiability`,
the unrestricted recovery in this claim exists exactly when

```text
E_S = 0 whenever intersection_(a not in S) ker h'_a = {0}.
```

This is a global support requirement, not an estimate of the marginal flag
probabilities. `identical-flag-marginals-can-disagree-on-exactifiability`
shows that even exactly matching marginal cost bounds cannot certify it.
The criterion does not find the kernel vectors efficiently or preserve the
logical witness; those stronger recovery demands require separate proofs
if a proposed construction uses them.

- **Knill--Laflamme recovery.**  For a correctable error family `{E_alpha}`
  with code projector `P`, the condition `P E_alpha^* E_beta P = c_(alpha beta) P`
  gives, after diagonalizing `c`, a coherent recovery of the form
  `R E_alpha P = P tensor |s_alpha>`, which is exactly the separation of the
  logical algebra from the syndrome register that (EXA1) wants -- the
  syndrome can be tested without learning the witness.  What it does not give
  is that the recovered state satisfies the *parent Hamiltonian terms* off
  `S` exactly, nor that the recovery is implementable at bounded horizon.
  Both are the missing quantitative half, and neither follows from the
  Knill--Laflamme conditions alone; no route is written on that basis.
- **Teleportation at every gate, making Bell outcomes explicit.**  Makes the
  computation deterministic only by pushing corrections forward, and
  localizing the final acceptance observable then reintroduces the nonlocal
  computation constraint.  Deferred as circular.
