---
rg: 2
id: rank-modelled-coefficients-violate-two-root-identities
kind: claim
title: Every coefficient ring with a unital rank model has a rank model of EL_3 violating the two-root identity
invalidates: [two-root-identity-by-restriction-to-dyadic-constants]
distinct_from:
  fd-represented-coefficients-violate-two-root-identities: that needs a unital homomorphism into some M_n(F_p) and uses the regular representation of a finite image; this needs only a unital homomorphism into a rank ultraproduct and uses the natural tensor square, so it covers coefficient rings with no finite-dimensional representation, such as the dyadic constants of the Leavitt algebra.
artifacts:
  - research/artifacts/el3-two-root-self-similarity-2026-09-12.md
---

**ESTABLISHED** (proof route `rank-modelled-coefficients-violation-proof`; artifact Section 4).
Let `T` be a unital ring and `phi : T -> M_omega` a unital ring homomorphism into a rank
ultraproduct over a field of characteristic `p`. Then `EL_3(T)` has a homomorphism into the unit
group of a rank ultraproduct over the same field in which the unit root elements satisfy

```text
rk( (x_23(1) - 1)(x_12(1) - 1) ) = 2/9 .
```

The model is the natural tensor square: `N_ab = E_ab (x) 1 + 1 (x) E_ab + E_ab (x) E_ab`, so
`N_23 N_12 = E_23 (x) E_12 + E_12 (x) E_23`.

**Consequences.**
- No argument using only group relations among elements of `EL_3(T)`, for a subring `T` of the
  coefficient ring that has a unital rank model, can prove
  `rank-models-of-el3-satisfy-the-two-root-identities`.
- The dyadic constants `D = colim M_(2^k)(F_2)` of `L_(F_2)(1,2)` are such a `T`. They carry
  every uniform self-similar relation: the branch endomorphisms `iota_i`, the swap `diag(w,w,w)`,
  `x_ab(1) = iota_0(x_ab(1)) iota_1(x_ab(1))`, and the constant block coordinates. So
  `dyadic-constant-el3-rank-models-satisfy-two-root-identity` is false, and the route
  `two-root-identity-by-restriction-to-dyadic-constants` is dead.
- A proof must use relations whose coefficient subring has no unital rank model. `D` together
  with `s_0, t_0` already generates the whole Leavitt algebra.
