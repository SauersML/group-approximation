---
rg: 2
id: leavitt-unit-group-algebra-is-prime
kind: claim
title: The group algebra of the binary Leavitt unit group is a prime ring
distinct_from:
  connell-group-ring-primality: that is the general criterion, imported from Connell and true for every group and coefficient ring; this is the single instance, and its content is that this group satisfies the criterion's hypothesis.
  leavitt-unit-group-has-no-finite-normal-subgroup: that is the group-theoretic hypothesis, a statement about `R^x` with no group algebra in it; this is the ring-theoretic conclusion about `F_2[R^x]`.
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the evaluation map and its surjectivity; this is a structural property of the same algebra that says nothing about the map, and it is what kills a splitting of it.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

`S = F_2[G]` with `G = L_(F_2)(1,2)^x` is a **prime** ring: for two-sided
ideals `I, J` of `S`, `I J = 0` forces `I = 0` or `J = 0`.

Equivalently `Z(S) = F_2` and `S` has no pair of nonzero ideals annihilating
each other — the second form is what
`leavitt-evaluation-does-not-split-as-module-map` consumes.

## Why it is worth its own node

Because it is a *positive* structural fact about `F_2[R^x]`, and this lane has
almost none.  Everything else the graph owns about this algebra is either an
explicit small computation (an idempotent, a lift, a kernel element) or a
no-go.  Primality is neither: it constrains the whole algebra at once, and it
is the reason two different sufficient conditions for a one-sided inverse are
dead rather than merely unattempted.

It also explains, retrospectively, why the module-splitting lane looked
plausible for so long.  Nothing local obstructs a splitting — the idempotent
`p = sigma(1)` it would produce satisfies `p^2 = p`, `pi(p) = 1_R` and
`eps(p) = 0`, all consistent with the graph's other facts, and even makes
`Sp` a ring isomorphic to `R` under `pi`.  The obstruction is global: `Sp`
would be annihilated by the whole kernel, and a prime ring has no room for
two nonzero ideals with zero product.

## What it does not give

It says nothing about direct finiteness.  Prime rings are freely both
directly finite and directly infinite — `R` itself is prime and directly
infinite — so this is not evidence in either direction on
`leavitt-unit-group-algebra-not-directly-finite`.  Its content is exactly the
removal of one route, not a lean toward either answer.

It also does not give semiprimitivity, primitivity, or anything about
`J(S)`; the Jacobson radical of this algebra is still uncomputed, and
`leavitt-corner-kernel-not-jacobson-radical` only rules out one guess about
the corner's.
