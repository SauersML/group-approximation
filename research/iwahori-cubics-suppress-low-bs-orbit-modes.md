---
rg: 2
id: iwahori-cubics-suppress-low-bs-orbit-modes
kind: claim
title: The two Iwahori cubics suppress low BS orbit-frequency defect
distinct_from:
  weyl-defect-koopman-spectral-regularity: that asks for the fully weighted inverse estimate; this is a dyadic finite-cycle estimate whose extra positive exponent makes the inverse sum converge.
  iwahori-uniform-infinitesimal-rigidity: that proves a Jacobian gap at compatible congruence representations; this asks for the corresponding low-mode bound uniformly on the far periodic BS packets.
---

**OPEN REDUCED FINITE INEQUALITY.**  Use the exact `BS(1,4)` skeleton and
projected Weyl defect `e'` from
`weyl-defect-koopman-spectral-regularity`.  Let `psi=Ad(h)` on the regular
part of `Z={V}'`.  For dyadic `0<t<=1`, let

```text
P_t=1_(t/2 < |1-psi| <= t).                            (ICL1)
```

Here `(ICL1)` is ordinary spectral projection for the finite-dimensional
unitary Koopman operator.  Prove that there are universal
`epsilon_0>0,C<infinity` such that every full approximate Iwahori tuple has

```text
||P_t e'||_2^2 <= C delta^2 t^(2+epsilon_0)             (ICL2)
```

for every `t`, after removing the fixed algebra.  It is enough to take
`epsilon_0=1`.

On a fourth-power cycle of length `L`, `(ICL2)` is the completely finite
Fourier statement

```text
sum_(j: t/2<|1-exp(2 pi i j/L)|<=t) |hat e'_(L,j)|^2
 <= C delta^2 t^(2+epsilon_0).                          (ICL3)
```

The packet in `bs14-periodic-koopman-modes-refute-skeleton-regularity`
shows that `(ICL2)` is false using the BS relation alone: its first mode has
mass proportional to `t^2`, with no extra exponent.  Thus `(ICL2)` asks for
exactly one quantitative gain from the non-amenable part of the
presentation.  In the square-root presentation this means the involution
and the two words

```text
(x s^2)^3,                    (x r s)^3.                (ICL4)
```

must charge the first orbit-frequency modes of every long periodic core.

This is strictly localized compared with the full local-global repair
problem: it does not ask to round `x`, match packet multiplicities, or build
the correction.  It asks only for the dyadic Fourier-energy inequality
`(ICL3)`.  At compatible congruence points its linearized form follows from
`iwahori-uniform-infinitesimal-rigidity`; the open content is uniformity on
the far/outlier packets.

## Attempts

- **Use the BS shift or atomless base trace alone.**  This is refuted exactly
  by `bs14-periodic-koopman-modes-refute-skeleton-regularity`; its first mode
  saturates exponent two and survives along growing exact packets.
- **Use the compatible-point Jacobian gap.**  This works only inside a
  uniform tube around a congruence representation.  Far packets need not
  extend exactly in their own dimension.  A proof must evaluate the two
  cubic Fox rows directly on low cyclic modes while permitting flexible
  boundary coupling between heterogeneous packets.

