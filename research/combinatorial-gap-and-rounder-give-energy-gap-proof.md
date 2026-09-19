---
rg: 2
id: combinatorial-gap-and-rounder-give-energy-gap-proof
kind: route
title: Average the rounder cost against the combinatorial floor, then invert with a constant instrument
target: combinatorial-gap-and-rounder-give-energy-gap
requires: []
---

**Forward.**  Fix a normalized `rho` and run the rounder.  Every outcome of
nonzero probability delivers a normalized `sigma_S` exactly satisfying all
terms outside `S`, so combinatorial soundness applies **pointwise** and gives
`|S| >= beta m` for each such outcome.  Taking expectations and using (CR1),

```text
beta m <= E|S| <= C sum_a Tr(h_a rho) = C m Tr(H rho).
```

Divide by `C m`.  Since `rho` was arbitrary, `lambda_min(H) >= beta/C`, which
is (CR2).

**Converse.**  The minimum in (CR3) is attained and `s* <= m`, because
`S = [m]` makes the exactness condition vacuous.  Let `sigma*` attain it.
The instrument

```text
rho |--> (discard rho; output the fixed label S*, prepare sigma*)
```

is CPTP and satisfies clause (1) of the rounder definition by construction.
Its cost clause is `s* <= C sum_a Tr(h_a rho)` for **every** `rho`, i.e.

```text
s* <= C m inf_rho Tr(H rho) = C m lambda_min(H),
```

so it is a `C`-rounder exactly when `C >= s*/(m lambda_min(H))`.  Conversely
any `C`-rounder, applied to a ground state, has some outcome with
`|S| >= s*` by the definition of `s*`, hence
`s* <= E|S| <= C m lambda_min(H)`.  The two inequalities give (CR4).

The forward direction is (CR4)'s `>=` half specialized to `s* >= beta m`.
