---
rg: 2
id: index-three-corner-placement-holds-only-modulo-two-root-defects
kind: claim
title: The index-three corner placement of the rank-four plan equals its honest value plus a same-row and a reversed root product, and never uses the fourth index
distinct_from:
  el3-two-root-violation-splits-over-leavitt-branches: that is the EL_3 defect factorization of one commutator in characteristic two; this applies a characteristic-free swap identity twice to the corner products S(b) = n_31(b)n_13(1), T(a) = n_34(a)n_43(1) and isolates their two deviation terms.
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the isometry commutator identities on one root pair and why a single Peirce corner is circular; this shows that the placement across two root pairs sharing index 3 reduces to the same telescoping, with index 4 replaceable by 2.
  rank-four-isometry-relations-give-corner-cuntz-family: that asserts a non-circular four-index assembly; this fixes one opposite-root placement for it and shows its orthogonality relations hold only modulo block-support failures.
artifacts:
  - research/artifacts/rank-four-orthogonality-check-2026-09-12.md
---

**ESTABLISHED** (route `index-three-corner-placement-identity-proof`; artifact Section 3).

**Setting.**
- `R` and `M` are unital rings, and `sigma : EL_4(R) -> M^x` a homomorphism.
- `X_ij(r) = sigma(x_ij(r))` and `n_ij(r) = X_ij(r) - 1`.
- The placement is `S(b) = n_31(b) n_13(1)` and `T(a) = n_34(a) n_43(1)`.

**Identity.** For all `a, b` in `R`,

```text
T(a) S(b) = n_31(ab) X_41(b) X_34(a) X_31(b) X_43(1) n_13(1)
          + n_31(b) n_34(a) n_43(1) n_13(1)
          + n_41(b) n_34(a) X_31(b) X_43(1) n_13(1) .
```

**Consequences.**
1. **Cross terms.** When `ab = 0` only the last two deviation terms remain.
2. **Block-support failures.** Each deviation term contains a product `n_ab(r) n_cd(r')` with
   `b != c`, the same-row product `n_31(b) n_34(a)` or the reversed product `n_41(b) n_34(a)`.
   These vanish in honest models `sigma(x_ij(r)) = 1 + rho(r) E_ij`, where
   `T(a) S(b) = rho(ab) E_33`.
3. **No fourth index.** Replacing index 4 by 2 gives the same identity inside `EL_3(R)`.

**What this means for the plan.**
- **Circularity.** For this placement, relation (i) of the plan is the honest value plus
  block-support deviations. Bounding those deviations under `N_23 N_12 != 0` is the gate itself,
  and the fourth index adds nothing.
- **Coefficients alone don't force the cross term.** Take the left regular representation of
  `EL_4(M_2(F_2)) = SL_8(F_2)` with `t_1 -> E_22` and `s_0 -> E_11`. There the cross term
  `T(t_1) S(s_0)` is nonzero. So its vanishing does not follow from the Steinberg relations and
  `t_1 s_0 = 0` alone.

## Attempts

Established; see the route. Artifact Section 4 records where check (i) stops.
