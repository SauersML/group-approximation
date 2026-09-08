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

**ESTABLISHED (ordinary mathematical proof; not a Lean certificate).**
Let `H = (1/m) sum_a h_a` on a nonzero finite-dimensional Hilbert space,
with `m >= 1` and `0 <= h_a <= I`. Rounder constants satisfy `C >= 0`.

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

**Forward direction.**  Combinatorial gap `beta > 0` plus a `C`-rounder
forces `C > 0` and gives

```text
lambda_min(H) >= beta / C.                                      (CR2)
```

**Converse, and what it costs the attack.**  Put

```text
s* = min{ |S| : some normalized sigma has Tr(h_a sigma)=0, a not in S }. (CR3)
```

Then the least admissible rounder constant is exactly

```text
min{C >= 0 : a C-rounder for H exists}
  = 0                           if lambda_min(H) = 0,
  = s* / (m lambda_min(H))       if lambda_min(H) > 0.         (CR4)
```

In finite dimension, `lambda_min(H) = 0` holds exactly when `s* = 0`:
a ground state then satisfies every positive term. Discarding the input and
preparing that state with the empty fault set is a `0`-rounder. There is no
`+infinity` case under these hypotheses. This corrects the previous `0/0`
convention (2026-09-07).

For a **family with combinatorial gap bounded below by a positive constant**,
a uniform `O(1)` rounder constant is equivalent to a uniform positive
normalized ground-energy lower bound. Indeed `beta <= s*/m <= 1`.
The family and positive-gap qualifiers are essential: on one fixed finite
instance a finite rounder constant always exists, and frustration-free
families have zero-cost rounders and zero ground energy. This equivalence
concerns the NO-side energy floor, not the full QMA-hardness reduction or
its YES-side promise.

Definition (CR1) imposes no locality, no efficiency, and no
closeness-to-input requirement on the instrument. Bare existence supplies
no uniform cost bound: using the minimizing constant instrument requires
exactly the energy floor one is trying to establish. A successful argument
must prove a uniform bound, for example through the structure demanded by
`commuting-syndrome-domination-gives-a-rounder`: the fault set must be the
outcome of a joint measurement of commuting local projectors of bounded
overlap. The relevant construction problems are
`local-syndrome-port-domination-at-each-gadget` and
`syndrome-conditioned-exactifier-exists`. This identity does not prove
those statements equivalent to QPCP, nor does it discharge the separate
amplifier and completeness obligations.
