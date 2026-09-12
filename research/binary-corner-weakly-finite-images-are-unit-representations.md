---
rg: 2
id: binary-corner-weakly-finite-images-are-unit-representations
kind: claim
title: The binary complement corner has a weakly finite image exactly when the Leavitt unit group represents in a weakly finite ring of characteristic two
distinct_from:
  rank-condition-rings-have-weakly-finite-images: that is a general ring theorem turning the rank condition into a weakly finite quotient; this identifies weakly finite quotients of the specific corner T with weakly finite representations of R^x, using the halving homomorphism and simplicity.
  binary-complement-corner-rank-functions-pull-back-to-units: that transports Sylvester rank functions between T and F_2[R^x]; this transports weak finiteness, which needs no rank function.
artifacts:
  - research/artifacts/binary-weakly-finite-representations-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-wf-binary`; verification requested from `w4-vf-linear-b`) by
`binary-corner-weakly-finite-unit-representation-proof`.

Let `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, with `g`, `e`, `f = 1 - e` and `T = f A f` as in
`binary-cyclic-corner-full-iff-complement-corner-has-no-state`. The following are equivalent.
1. `T` has a nonzero weakly finite homomorphic image.
2. Some unital ring homomorphism `φ : A -> W` into a weakly finite ring has `φ([g]) != 1`.
3. `G` has a nontrivial homomorphism into the unit group of a weakly finite ring of characteristic two.

**Mechanism** (artifact Section 1).
- **1 => 2.** Compose the quotient with the unital halving homomorphism `ψ'(x) = f D(x)`. If `[g]` went to
  `1`, the idempotents `f_(K_3) + f_(K_4)` would die, and so would `f`, because the `f_K` are equivalent
  inside `T`.
- **2 => 1.** `φ(f) = u + u² != 0` for `u = φ([g]) != 1`, and `φ(T)` sits with the same unit inside the
  weakly finite corner `φ(f) W φ(f)`.
- **2 <=> 3.** Simplicity of `G` (`binary-leavitt-unit-group-is-simple`).

**Consequence.** Together with Theorems B and C, `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`
holds iff `L_(F_2)(1,2)^x` has no nontrivial homomorphism into the unit group of any weakly finite ring of
characteristic two (artifact Theorem W). The direction from fullness is elementary.
