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

Since `beta m > 0`, this excludes `C = 0`. Divide by `C m`.
Since `rho` was arbitrary, `lambda_min(H) >= beta/C`, which
is (CR2).

**Zero-energy case.** In finite dimension there is a normalized ground state
`sigma_0`. If `lambda_min(H) = 0`, the nonnegative numbers
`Tr(h_a sigma_0)` sum to zero, so each is zero and `s* = 0`.
Conversely, `s* = 0` supplies a state of zero energy, so positivity gives
`lambda_min(H) = 0`. The constant instrument preparing `sigma_0` with
`S = empty` has cost zero on every input, proving the first branch of (CR4).

**Positive-energy case.** Now assume `lambda_min(H) > 0`.
The minimum in (CR3) is attained and `s* <= m`, because
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
For a family with `s*/m >= beta > 0`, the identity gives
`beta/lambda_min(H) <= C_min <= 1/lambda_min(H)`, proving the stated
equivalence of uniform bounds. It does not construct a hardness reduction.
