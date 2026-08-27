---
rg: 2
id: arithmetic-finite-actions-are-lambda-generated
kind: claim
title: Every finite action of the S-arithmetic group has the same image as its integral subgroup - permutation co-density
artifacts:
  - research/artifacts/wreath-permutation-collapse-2026-08-22.md
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that is finite-DIMENSIONAL-representation co-density of the SL_2 pair used by the HNN theorem; this is the PERMUTATION-action form at SL_3 - equal images in symmetric groups - the input the wreath permutation collapse needs, proved from Margulis plus CSP plus strong approximation rather than from unitary representation theory.
  arithmetic-integral-subgroup-is-incompressible: that shows the compression semigroup is trivial, fencing off Kun-Thom; this shows finite actions cannot separate the subgroup from the group, the co-density that replaces compression in the permutation collapse.
---

THEOREM.  Let `Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/3])`.  For every
action `tau` of `Gamma` on a finite set `V`:

```text
tau(Lambda) = tau(Gamma)  as subgroups of Sym(V).            (PC1)
```

In particular every `Gamma`-orbit is a `Lambda`-orbit, and the
centralizer of `tau(Lambda)` in `Sym(V)` equals the centralizer of
`tau(Gamma)`.

Proof (complete in the artifact, Theorem C): finite transitive actions
are `Gamma/H` with `H` finite index; Margulis normal subgroup property
plus the congruence subgroup property for `SL_3(Z[1/S])` put a
principal congruence subgroup `Gamma(m)`, `gcd(m,3) = 1`, inside `H`;
the action factors through `SL_3(Z/m)`, onto which `Lambda` surjects —
jointly across the finitely many levels of the components by strong
approximation (the closure of `SL_3(Z)` in `prod_{q != 3} SL_3(Z_q)`
is everything).

This is the permutation shadow of the co-density that runs the whole
arithmetic program: no finite action can see the difference between
`Lambda` and `Gamma`.  Consumed by
`wreath-nonsofic-from-flexible-p-stability`; it is also the reason the
coset Schreier graph of `Gamma/Lambda` admits no finite equivariant
quotients at all (every equivariant finite quotient is a point), which
is what makes the soficity of the coset action genuinely hard in both
directions.
