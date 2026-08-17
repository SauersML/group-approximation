---
rg: 2
id: stable-finiteness-failure-from-module-splitting
kind: route
title: Extend right multiplication by s_0 across a module complement
target: leavitt-group-algebra-not-stably-finite
requires: [leavitt-evaluation-splits-as-module-map, leavitt-evaluation-surjective-with-nonzero-kernel]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

Write `S = F_2[G]`, `pi : S ->> R` for the evaluation map, `K = ker(pi)`.  A
left `S`-linear `sigma : R -> S` with `pi . sigma = id_R` gives a
decomposition of left `S`-modules

    S = sigma(R) (+) K,

with `pi` identifying `sigma(R)` with `R`.

On `R`, put `f(r) = r s_0` and `g(r) = r t_0`.  Both are left `S`-linear for
the module structure through `pi`, since scalars act on the left.  They
satisfy `f(g(r)) = r t_0 s_0 = r`, so `f . g = id_R`, while `g . f != id_R`
because `g(f(1)) = s_0 t_0 != 1` — otherwise `s_1 t_1 = 0` and
`0 = t_1 (s_1 t_1) s_1 = (t_1 s_1)^2 = 1`.

Extend by the identity across the complement:

    F = f (+) id_K,        H = g (+) id_K.

These are left `S`-module endomorphisms of the left regular module `S`, with
`F . H = id_S` and `H . F != id_S`.  Every endomorphism of the left regular
module is right multiplication by its value at `1`, so with `a = F(1)` and
`b = H(1)` this reads

    b a = 1,      a b != 1

in `S`, which is the target at `n = 1`.

## What the route consumes and what it does not

Only a **module** splitting is used; multiplicativity of `sigma` is never
needed, which is fortunate, since a ring section is impossible
(`leavitt-evaluation-has-no-ring-section`).  The second prerequisite supplies
the map `pi` itself and its surjectivity; the splitting hypothesis carries
the rest.
