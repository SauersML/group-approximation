---
rg: 2
id: finite-involution-corner-sylow-permutation-proof
kind: route
title: Use odd Sylow coset representations to eliminate every odd common negative rank divisor
target: finite-involution-corner-width-is-power-of-two
requires: []
artifacts:
  - research/artifacts/finite-involution-corner-width-is-power-of-two-2026-09-08.md
---

Every representation of the finite group is a direct sum of complex
irreducibles, so `g_J` divides its negative involution rank. The
regular representation has rank `|F|/2`, since left multiplication
by `J` is a permutation consisting of pairs. Thus `g_J` divides
`|F|/2` and is positive.

Fix an odd prime `p` dividing `|F|` and take a Sylow `p`-subgroup
`P`. The involution acts freely on `F/P`: a fixed coset would
put a conjugate of `J` in the odd-order group `P`. Therefore the
negative rank of the permutation representation on these cosets is
`[F:P]/2`. This integer is prime to `p`, because `[F:P]` is
prime to `p` and `p` is odd. Hence `p` cannot divide `g_J`.
Every possible odd prime divisor has been excluded, and the bound
on the remaining two-part follows from `g_J` dividing `|F|/2`.

Under finite-group algebra decomposition, the projection `q` has
rank `m_rho` in the irreducible matrix block for `rho`. Hence

```text
q C[F] q ~= directSum_(rho:m_rho>0) M_(m_rho)(C).
```

A unital representation of `M_D(C)` on a space of dimension
`m_rho` is a direct sum of its `D`-dimensional defining module,
so it exists exactly when `D` divides `m_rho`. Applying this to
each nonzero summand proves necessity. Conversely, if all these
divisibilities hold, the maps `x -> x tensor I_(m_rho/D)` in
each summand assemble into the required unital star homomorphism.
This proves both the exact criterion and its power-of-two consequence.
