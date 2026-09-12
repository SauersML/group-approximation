---
rg: 2
id: nonhyperlinear-bloop-strict-augmentation-energy
kind: claim
title: Construct a strict no-CE energy bound in an explicit full augmentation corner
distinct_from:
  nonhyperlinear-bloop-finite-augmentation-corner: that asks for exact finite-support BCS identities; this asks for one positive energy bound strictly below the robust matrix threshold.
artifacts:
  - research/artifacts/strict-bcs-energy-in-full-augmentation-corner-2026-09-08.md
---

For the fixed BCS `B_loop`, construct an explicit countable group
`G`, an embedded nontrivial finite subgroup `K`, a named `k!=1`
in `K`, and self-adjoint contractions `a_x` in the actual corner
`q C*_max(G)q`, where `q=1-|K|^-1 sum_(h in K)h`, such that

```text
E_B(a)<=c q,                 0<=c<beta.
```

Here `E_B` and the dimension-independent contraction gap `beta`
are those of `strict-bcs-energy-in-augmentation-corner-kills-mf`.
Both the maximal-C-star order inequality and the strict comparison
with `beta` must be proved. Explicit finite-support sums-of-squares
identities as in the artifact are one sufficient certificate form.

This gate is OPEN. A full maximal-C-star corner map would suffice
by norm density; a map into a quotient does not. No strict bound
of this kind is currently constructed. Any successful host would
already be nonhyperlinear, by its positive canonical corner trace.
The known finite-window wreath host cannot meet this requirement.

## Attempts

2026-09-08: The [strict-energy artifact](artifacts/strict-bcs-energy-in-full-augmentation-corner-2026-09-08.md)
derives the contraction gap by spectral rounding and proves that a bound
`E_B(a)<=c q` with `c<beta` in the actual full corner would kill the finite
subgroup in every matrix corona. It gives finite-support sums-of-squares
identities as a sufficient certificate and shows that an exact map into
the full corner would yield a strict bound by maximal-norm approximation.
Neither construction has been supplied. A map into a quotient does not
provide the required full-corner elements, and the positive canonical
corner trace excludes every hyperlinear host. The missing step remains
an explicit host and a certified strict inequality inside its full corner.
