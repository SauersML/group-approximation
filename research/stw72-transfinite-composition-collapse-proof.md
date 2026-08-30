---
rg: 2
id: stw72-transfinite-composition-collapse-proof
kind: route
title: Run extension permanence at successors and inductive-limit permanence at limit ordinals
target: stw72-transfinite-simple-layer-wpi-is-purely-infinite
requires:
  - stw72-chain-ideal-wpi-is-purely-infinite
artifacts:
  - research/artifacts/stw72-transfinite-composition-collapse-audit-2026-08-30.md
---

Weak pure infiniteness passes to closed ideals and quotients.  Hence every
`I_beta` is weakly purely infinite and every successor layer

```text
Q_beta=I_(beta+1)/I_beta
```

is weakly purely infinite.  Since `Q_beta` is simple, its closed ideal
lattice is linearly ordered.  The established chain-ideal theorem
`stw72-chain-ideal-wpi-is-purely-infinite` therefore makes every `Q_beta`
purely infinite.

We now prove by transfinite induction that every `I_beta` is purely infinite,
using the Kirchberg--Rordam permanence theorems for their nonsimple notion of
pure infiniteness.  The zero algebra is purely infinite under the standard
vacuous convention.  At a successor ordinal, the exact sequence

```text
0 -> I_beta -> I_(beta+1) -> Q_beta -> 0
```

has purely infinite ideal and quotient, so extension permanence makes
`I_(beta+1)` purely infinite.

At a nonzero limit ordinal `lambda`, continuity of the series identifies
`I_lambda` with the C-star inductive limit of the directed system

```text
(I_beta)_(beta<lambda)
```

whose connecting maps are the inclusions.  Every earlier term is purely
infinite by induction, and pure infiniteness is preserved by C-star
inductive limits.  Thus `I_lambda` is purely infinite.  This limit step is
valid for an arbitrary ordinal: the permanence theorem is for directed
inductive limits, not only sequential ones.  Taking `beta=alpha` gives that
`A` is purely infinite.

For the example in the claim, let

```text
I_beta=c_0(beta,O_infinity) inside c_0(alpha,O_infinity).
```

The quotient at `beta+1` is the new coordinate copy of `O_infinity`.  If
`lambda` is a limit ordinal, every element of `c_0(lambda,O_infinity)` is
uniformly approximated by a finitely supported element, whose finite support
is contained in some `beta<lambda`; hence the filtration is continuous.
This also verifies directly that the hypothesis is not a disguised finite-
ideal-lattice condition.
