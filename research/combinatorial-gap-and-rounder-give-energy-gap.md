---
rg: 2
id: combinatorial-gap-and-rounder-give-energy-gap
kind: claim
title: Constant-cost exactification transfers combinatorial gap to energy gap, and conversely
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  classical-pcp-gap-is-not-tracial-pvm-gap: that exhibits a BCS on which classical unsatisfiability and tracial forbidden mass point in opposite directions; this is a two-sided identity between the least rounder constant, the exact combinatorial defect, and the ground energy of one fixed Hamiltonian.
---

**ESTABLISHED.**  Let `H = (1/m) sum_a h_a` with `0 <= h_a <= I`.

**Combinatorial gap.**  `H` has combinatorial gap at least `beta` if every
normalized `sigma` and every `S` with `Tr(h_a sigma) = 0` for all `a not in S`
has `|S| >= beta m`.  (For `h_a >= 0` and `sigma >= 0`, `Tr(h_a sigma) = 0`
is equivalent to `h_a sigma = 0`, so the two spellings of exactness agree.)

**`C`-rounder.**  A CPTP instrument which on every input `rho` outputs a
classical set `S` and a normalized `sigma_S` with `Tr(h_a sigma_S) = 0` for
every `a not in S`, and

```text
E |S| <= C sum_a Tr(h_a rho).                                   (CR1)
```

**Forward direction.**  Combinatorial gap `beta` plus a `C`-rounder gives

```text
lambda_min(H) >= beta / C.                                      (CR2)
```

**Converse, and what it costs the attack.**  Put

```text
s* = min{ |S| : some normalized sigma has Tr(h_a sigma)=0, a not in S }. (CR3)
```

Then the least admissible rounder constant is exactly

```text
inf{C : a C-rounder for H exists} = s* / (m lambda_min(H)),     (CR4)
```

with the convention that the right side is `+infinity` when
`lambda_min(H) = 0`.  So for a fixed Hamiltonian, **"a constant-cost rounder
exists" is logically equivalent to "the energy gap is constant"**.

Definition (CR1) imposes no locality, no efficiency, and no
closeness-to-input requirement on the instrument, and without one of those
(CR2) renames its own conclusion.  Any route which supplies a rounder by
bare existence is a restatement.  The content of the attack therefore lies
entirely in the *structure* demanded of the rounder by
`commuting-syndrome-domination-gives-a-rounder`: the fault set must be the
outcome of a joint measurement of commuting local projectors of bounded
overlap.  That structured statement is
`local-syndrome-port-domination-at-each-gadget`, and it is the only node in
this region whose truth is not already equivalent to
`quantum-pcp-constant-gap-local-hamiltonian`.
