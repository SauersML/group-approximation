---
rg: 2
id: lcs-perfect-quantum-completeness-re-hardness
kind: claim
title: Binary linear-constraint protocols have RE hardness with perfect quantum completeness and constant soundness
root: true
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: That older weak interface only requires commuting completeness and input-dependent strict quantum soundness, so a constant separating game satisfies it; this requires quantum completeness, one uniform gap, and efficient succinct verifiers.
  taller-vidick-lcs-re-hardness: That gives completeness 1 minus epsilon for each fixed positive epsilon; this requires completeness exactly one.
  leavitt-lcs-game-with-certified-numerical-gap: That asks for one explicit commuting versus quantum separating game; this asks for a halting-sensitive family with positive quantum models on the halting side.
artifacts:
  - research/artifacts/hyperbolic-and-perfect-lcs-campaign-2026-09-20.md
  - research/artifacts/lcs-perfect-completeness-attack-2026-09-20.md
  - research/artifacts/lcs-halting-switch-audit-2026-09-20.md
---

OPEN. There exist a constant rational 0<=s<1, a constant answer-length bound,
and uniform polynomial-time sampling and verification algorithms defining
finite binary LCS games L_x, with polynomial-length questions, such that

```
x is a halting machine code     => omega_q(L_x)=1,
x is a nonhalting machine code  => omega_q(L_x)<=s.
```

Here omega_q is the supremum over finite-dimensional entangled strategies.
Value one need not be attained by a single finite-dimensional strategy;
requiring an attained perfect strategy is a sufficient stronger goal.
Commuting-operator value one alone is insufficient. The source's synchronous
formulation is also relevant, but conversion to the displayed unrestricted
soundness must be justified, not silently identified with it.

This is the perfect-completeness endpoint discussed by Taller--Vidick,
arXiv:2507.22444v2, introduction and Section 5, rechecked 2026-09-20.
No resolution was found in this bounded source check. One fixed
nonhyperlinear group does not supply this family or its complexity bounds.

## Attempts

2026-09-20: the established fixed binary LCS gap obtained using Jihao Liu's
internality, Andreas Thom's normalization and the Paddock--Slofstra
reduction closes only the older commuting-completeness interface. Its
constant map fails the halting quantum-completeness requirement here.

The published positive-noise test cannot be made perfectly complete by
reweighting: its support contains a two-row sign contradiction. Setting
noise to zero changes the equations and removes the quantitative Fourier
decoder. The new attack therefore examines an actual zero-noise decoder,
or a different machine-dependent construction, rather than a limit of
positive-noise presentations.

A merely computable finite-table reduction is useful intermediate work,
but does not by itself supply polynomial-time succinct sampling. Likewise
an input-dependent positive gap is not the fixed s required above.

The next wave established two sharper obstructions, not a solution:

- [[lcs-pc-zero-noise-coloring-cheat]] gives a globally compatible perfect
  classical strategy for the unchanged noiseless TV test on repeated K4
  three-colouring sources whose quantum value tends to zero. Merely
  improving that generic decoder cannot suffice. A source-specific
  exclusion or a genuinely changed test is necessary.
- [[lcs-switch-marked-seed-transport-is-re]] rules out certifying every
  nonhalting output sign by finite normal-closure combinations of images
  of killed marks from any recursively enumerable library of finite
  seeds, while preserving the sign in a matrix-ultraproduct model on
  halting inputs. The certificates would enumerate coHALT. This blocks
  an implementation by the fixed Liu seed, not all hardness reductions.

The constructive continuation proves
`lcs-construct-weighted-conjugacy-to-lcs`: a bounded-size weighted
conjugacy gadget preserves perfect quantum completeness and transfers
a uniform matrix-energy gap, including to unrestricted quantum
strategies. The new route
`lcs-perfect-hardness-from-weighted-conjugacy-source` checks exact
polynomial-time sampling as well. Its single unresolved source family
is `lcs-weighted-conjugacy-halting-gap-source`; the existence of that
family is not inferred from the compiler.

The shared-anchor repair also has an explicit global finite model on
K4, recorded in `lcs-anchor-shared-pauli-splitters-have-k4-model`.
And `ce-affine-decoder-positive-model-forces-safe-support` rules out
using a nonhyperlinear host alone to rescue universally CE-exact affine
decoding on affine-unsafe positive instances. Non-affine source decoding
and an actual halting-positive word construction remain live obligations.
