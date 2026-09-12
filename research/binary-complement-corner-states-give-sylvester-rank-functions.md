---
rg: 2
id: binary-complement-corner-states-give-sylvester-rank-functions
kind: claim
title: If the binary complement corner satisfies the rank condition, it carries a normalized Sylvester rank function
distinct_from:
  ternary-anti-central-states-give-sylvester-rank-functions: that is step U1 for the central ternary factor eps_- F_3[G_3]; this is the same step for the non-central binary corner (1 - e) F_2[R^x] (1 - e), where no character splits off the augmentation.
  binary-complement-corner-rank-functions-pull-back-to-units: that transports rank functions between the corner and the group algebra; this asks that a K_0 state on the corner be realized by a rank function at all.
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `G = R^x`, `e = 1 + [g] + [g²]` for the ternary permutation unit `g`,
`f = 1 - e`, and `T = f F_2[G] f`. If `(K_0(T), [T])` admits a state, then `T` carries a Sylvester matrix
rank function `N` with `N(f) = 1`.

**Why it matters.** It is step U1 of the binary state upgrade (artifact Corollary C.1).
- **The corner.** By `binary-cyclic-corner-full-iff-complement-corner-has-no-state`, the binary cyclic
  corner is full iff `T` has no state.
- **The gate.** By `binary-complement-corner-rank-functions-pull-back-to-units`, the Sylvester two-root gate
  `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect` holds iff `T` has no normalized rank
  function.
- **Together.** This claim makes the two coincide. The gate then refutes Gottschalk through Kaplansky
  failure for `R^x` (route `binary-counterexample-from-rank-kill-and-state-realization`).

## Attempts

- 2026-09-12 `w5-binary-upg`: proposed as step U1 of the binary chain (artifact Sections 3–4).
  - **Division rings are dead.** `T` has no unital homomorphism into `M_n(D)` for any division ring `D` of
    characteristic two (artifact Corollary 4.2). So a Cohn–Malcolmson localization into a division ring
    cannot realize a state.
  - **Normalization is available.** If any state exists, one can be chosen with
    `s ∘ K_0(ψ'|_T) = (2/3) s`, with `ψ'(x) = f D(x)` (artifact Proposition 4.1).
  - **The additive shadow is consistent.** The lifted trace, normalized, satisfies every tower relation, but
    it is not positive.
  - **Where it stops.** It is the same general ring question as the ternary U1: does the rank condition, or a
    state, yield a Sylvester matrix rank function? A general counterexample ring would not kill this
    instance, and no input specific to `T` beyond the halving homomorphism is known. The literature check
    belongs to `w4-upg-kill`.
