---
rg: 2
id: dyadic-constant-el3-rank-models-satisfy-two-root-identity
kind: claim
title: Every characteristic-two rank model of EL_3 over the dyadic constants of the Leavitt algebra satisfies the two-root identity
refuted_by:
  - rank-modelled-coefficients-violate-two-root-identities
distinct_from:
  rank-models-of-el3-satisfy-the-two-root-identities: that is the open target over the whole Leavitt algebra; this is the stronger shortcut over the constant subring D = colim M_(2^k)(F_2), which would imply the target by restriction and is false.
artifacts:
  - research/artifacts/el3-two-root-self-similarity-2026-09-12.md
---

**REFUTED** by `rank-modelled-coefficients-violate-two-root-identities` (artifact Section 5,
Corollary 4).

**Statement (false).** Let `D` be the unital subring of `L_(F_2)(1,2)` spanned by the monomials
`s_u t_v` with `|u| = |v|`. Every homomorphism `sigma : EL_3(D) -> M^x` into a characteristic-two
rank ultraproduct satisfies `(sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1) = 0`.

**Why it looked plausible.** Every uniform self-similar relation lives in `EL_3(D)`: the branch
endomorphisms `iota_i`, the swap `diag(w,w,w)`, the doubling identity
`x_ab(1) = iota_0(x_ab(1)) iota_1(x_ab(1))`, and the constant block coordinates identifying
`EL_3(D_k)` with `SL_(3 2^k)(F_2)`.

**Why it is false.** `D ~= colim M_(2^k)(F_2)` has a unital rank model, `a -> a (x) I`. The natural
tensor square of `EL_3(D)` then has `N_23 N_12 = E_23 (x) E_12 + E_12 (x) E_23`, of rank `2/9`.

## Attempts

- **Uniform displacement counting on `SL_3(F_2)`** ([TR] Section 5): dies, a special case.
- **Iterating the branch split** (`el3-two-root-violation-splits-over-leavitt-branches`) over
  constants: gives only upper bounds, and the tensor-square model shows no lower bound can hold.
