---
rg: 2
id: leavitt-kazhdan-commutant-is-nonseparable
kind: claim
title: In every nontrivial matrix-ultraproduct model of the Leavitt configuration the Kazhdan relative commutant is non-separable
distinct_from:
  leavitt-kazhdan-relative-commutant-has-no-type-one-part: that proves the Kazhdan relative commutant is of type II_1 in any finite von Neumann algebra; this adds the ultraproduct input, countable saturation, and concludes that the commutant is non-separable, which excludes every separable candidate commutant.
---

**ESTABLISHED.** Use the nine-leaf configuration
`Gamma = EL_alpha(R) <= G = EL_D(R) <= L_(F_2)(1,2)^x` with compressor `u` and
`J = V_(1000) ~= V`, as in `leavitt-kazhdan-relative-commutant-has-no-type-one-part`.
Let `M = prod_omega M_(d_n)` (normalized traces, `omega` a free ultrafilter on
`N`) and let `sigma : G -> U(M)` satisfy `tau o sigma != 1`. Compress by the
central projection `q` of that node, so that the character is regular, and put
`A_0 = sigma(Gamma)' cap qMq`. Then

```text
A_0 is not separable in the 2-norm.                           (NS)
```

The same holds for every `A_k = sigma(u)^k A_0 sigma(u)^(-k)`.

**The general dichotomy used.** For a countable set `S` in a tracial matrix
ultraproduct `N = prod_omega M_(k_n)`, the relative commutant `S' cap N` is
separable if and only if it is purely atomic, a countable direct sum of matrix
algebras. The proof is a diagonal argument over `omega`, i.e. countable
saturation. So a relative commutant with a nonzero diffuse part is never
separable.

## Consequences for the unstable branch

- **Separable commutants are impossible.** No model of
  `binary-leavitt-unit-group-hyperlinear`, equivalently of
  `leavitt-steinberg-hs-unstable`, can have a separable Kazhdan commutant. In
  particular `A_0 = sigma(J)''`, or `A_0` equal to any separable algebra built
  from the complementary corner, is excluded. The commutant is always strictly
  and hugely larger than the complementary group factor.
- **Separability cannot detect a negative 6.2(a) instance.** By (13) of the
  heat-rounding artifact, the unstable branch needs a negative instance of
  Alekseev--Thom Open Problem 6.2(a).
  - **What such an instance is.** It is, by definition, a relative commutant
    that is not an ultraproduct of coordinate algebras.
  - **Two different algebras.** The commutant in (13) is the native corner
    `pi(L)' cap M` of a canonical `H`-model. It is not the nine-leaf
    `A_0 = sigma(Gamma)' cap qMq` of this node. The same proof makes both
    non-separable.
  - **So separability decides nothing.** Internal and non-internal type
    `II_1` commutants are both non-separable. For `A_0`, growth under the
    compressor, `A_0 <= A_1 ~= A_0`, has to happen without a slowly varying
    central height.
- **Scope.** Nothing here obstructs faithful models. Like the type-I screen, it
  fixes the shape any witness must have.

DERIVATION
leavitt-kazhdan-commutant-is-nonseparable-proof
