---
rg: 2
id: finite-morita-shift-detects-projective-difference-proof
kind: route
title: Read the cocycle difference on the finite coefficient action
target: finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres
requires:
  - deligne-triple-cover-fd-central-invisibility
  - maslov-mod3-gap-is-metaplectic-base-degree-six-gap
---

Write `alpha_theta(g,h)=exp(2 pi i theta b(g,h))`.  Applying
multiplicativity to `(FMS1)` gives

```text
v_g v_h
 = alpha_theta(g,h) alpha_phi(g,h)^(-1) v_(gh),         (FMS3)
```

after absorbing the permitted scalar one-cochain into `v`.  Hence the finite
coefficient action realizes `[alpha_(theta-phi)]`.  Conversely this is
exactly the coefficient used by the valid half-shift construction, so the
condition is sharp for generator-equivariant tensor shifts.

A finite equivariant Morita bimodule gives the same equation: compare the
left and right projective covariance relations on its finite coefficient
space.  Their scalar associators divide, yielding `(FMS3)`.  Stabilizing,
taking direct sums, conjugating, or compressing an invariant finite
coefficient subspace does not change the conclusion that the difference
class is finite-dimensionally realizable.

If the difference is `1/3` or `2/3`, this coefficient representation extends
along a section to a finite-dimensional representation of `E_3` with
nontrivial central character, contradicting
`deligne-triple-cover-fd-central-invisibility`.  If it is `1/6` or `5/6`,
the corresponding representation of `E_6` is nontrivial on its full finite
residual `<z^2>=Z/3`, as identified in
`maslov-mod3-gap-is-metaplectic-base-degree-six-gap`; a finite-dimensional
unitary image is residually finite, so the full finite residual must lie in
its kernel, another contradiction.

Exact representations obtained from finite quotients of `E_2` have only the
two central characters of its `Z/2`, so their multiplier classes are `0` or
`1/2`.  These classes form a subgroup and remain the only possibilities
under all the listed finite tensor/Morita operations.  This proves the
scoped no-go.

