---
rg: 2
id: rank-four-isometry-relations-give-corner-cuntz-family
kind: claim
title: A nonzero two-root defect assembles an order-two Leavitt family in a corner through the fourth EL_4 index
distinct_from:
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the isometry commutator relations on one root pair and shows the single-corner extraction is circular; this asserts the non-circular assembly it calls for, placing the four partial isometries on four distinct root pairs of EL_4(R).
  matrix-unit-rank-models-extract-ring-rank-models: that extracts a ring rank model after the matrix-unit hypothesis is granted; this produces the Leavitt family from a nonzero defect without assuming the matrix-unit or block form.
  el3-unit-root-matrix-units-iff-two-root-identities: that is the per-model equivalence between the two-root identities and the matrix-unit hypothesis; this is the construction that turns a violated identity into a corner Leavitt family.
artifacts:
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
---

**OPEN.** Let `K` be a finite field of characteristic `p`, `R = L_K(1,2)`, and
`sigma : R^x -> M^x` a rank model into a rank ultraproduct `M` over a field of characteristic `p`.
By `leavitt-gl-equals-el-and-perfect-unit-group`, `R^x = EL_4(R)`, so `sigma` is at the same time a
homomorphism of `EL_4(R)`. Write `n_IJ(a) = sigma(x_IJ(a)) - 1` for the positive roots of `EL_4`,
and `D = N_23 N_12` for the EL_3 unit two-root product.

If `D != 0`, then there are an idempotent `e in M` with `rk(e) > 0` and elements
`S_0, S_1, T_0, T_1 in eMe` with

```text
T_i S_j = delta_ij e   (i, j in {0,1}),      S_0 T_0 + S_1 T_1 = e .
```

That is, `eMe` contains a unital order-two Leavitt family, equivalently a unital ring homomorphism
`R -> eMe`.

## Why this is the decisive step

`eMe` is again a rank ultraproduct over a field of characteristic `p` (Fitting decomposition and
idempotent lifting; `el3-two-root-identities` Theorem D). So the conclusion contradicts
`leavitt-algebra-has-no-unital-rank-model`. Hence a nonzero defect is impossible, `N_23 N_12 = 0`,
and `leavitt-el3-triviality-via-rank-four-cuntz-family` finishes the instance.

The construction is the **non-circular corner Leavitt family** that
`leavitt-isometry-commutators-constrain-el3-rank-models` identifies as the whole content of the
gate. The obstruction there -- assembling the four isometries inside one Peirce corner is circular,
because telescoping them needs the block form, which is the gate -- is bypassed by placing them on
four distinct root pairs of `EL_4(R)`, available because `R^x = EL_4(R)` with no choice.

## Attempts

- **The fourth index is free (first lemma, in progress).** `R^x = EL_4(R)` by Khanh--Thanh, so the
  six `EL_4` positive-root maps `n_IJ` exist with no extension step. On distinct root pairs the
  isometry commutators of `leavitt-isometry-commutators-constrain-el3-rank-models` hold twice:
  `[x_12(t_i), x_23(s_j)] = x_13(delta_ij)` and `[x_23(t_i), x_34(s_j)] = x_24(delta_ij)`.
- **Cross frame (the new relation).** `x_14(abc)` is `[x_13(ab), x_34(c)]` and
  `[x_12(a), x_24(bc)]`, and `x_13(ab) = [x_12(a), x_23(b)]`, `x_24(bc) = [x_23(b), x_34(c)]`. The two
  readings give an operator associativity identity tying the `(1,2)-(2,3)` data to the
  `(2,3)-(3,4)` data through the shared middle index 3. The plan builds `S_j` from the creation data
  on `(1,2),(2,3)` and `T_i` from the annihilation data on `(2,3),(3,4)`; the products `T_i S_j` are
  read at index 3, which is genuinely shared rather than a single Peirce corner of one root pair.
- **What must be proved.** (a) `T_i S_j = delta_ij e` from the two isometry-commutator frames plus
  the cross relation; (b) `S_0 T_0 + S_1 T_1 = e` from `s_0 t_0 + s_1 t_1 = 1` via
  `1 + N_12 = (1 + n_12(e_0))(1 + n_12(e_1))` promoted to the frame; (c) `rk(e) = rk(D) > 0`, so a
  nonzero defect gives a nonzero corner.
- **Why prior dead ends do not apply.** Rank-values-only arguments are excluded
  (`scalar-two-root-rank-data-cannot-force-the-identity`), and this is an operator construction;
  finite-dimensional-coefficient models are excluded
  (`fd-represented-coefficients-violate-two-root-identities`), and this uses the Leavitt relations;
  the single-corner circularity is bypassed by the fourth index. Property (T) is not used.
- **Open.** The three checks (a)-(c). In particular the precise placement of `T_i` and `S_j` and the
  proof that `rk(e) = rk(D)` rather than a lower bound.
- **Lead pass (w3-strategist-gate, family R4 lead).**
  - Only `T_0 S_0 = e = T_1 S_1` and `T_1 S_0 = 0` are needed. Check (b), completeness, is not
    used in the contradiction (artifact L1).
  - Given the established nodes, this claim is equivalent to the gate, so its content is the
    construction. The first landing did not define `S_j`, `T_i` or `e`. The baseline `tau`
    candidate is the circular matrix-unit extraction (L2, L3).
  - Kaplansky calibration: an exact corner family inside `F_2[R^x]` would refute direct finiteness
    of `F_2[R^x]` and make `R^x` non-sofic (Elek--Szabo). So check (a) must use the regularity or
    rank of `M` at an intermediate step, not only group relations, the Leavitt relations and
    direct finiteness (L4a).
  - The adjacent "cannot see" and "is now a Steinberg identity" wording was an overclaim. `EL_4`
    relations are relations of the same group `EL_3(R)`.
- **Endpoint, quantitative (lane `w4-r4-approx`, 2026-09-12).** Sources:
  `toeplitz-isometry-defects-have-total-rank-at-least-one`, and Section 3 of
  `leavitt-ring-rank-approximability-collapse-2026-09-12.md`. This agrees with L1 of the lead pass and
  adds four points.
  - **Inequality.** For `S, T in eMe` and `X in Me`, every Sylvester matrix rank function satisfies
    `rk(X) <= rk(e - TS) + rk(XS)`. The proof is push-through by block elimination, then
    `X = X(e - ST) + (XS)T`.
  - **Check (c).** `T_1 S_1 = e` only certifies `T_1 != 0`, so any positive lower bound on `rk(T_1)` is
    enough. `rk(e) = rk(D)` is not needed.
  - **Finite level.** The inequality already holds in `M_n(k)` with normalized rank. Approximate
    relations suffice when their total defect is below `rk(T_1)`.
  - **Every finite `K`.** The endpoint needs no simplicity and no field hypothesis. This matters because
    `leavitt-algebra-has-no-unital-rank-model`, which `leavitt-el3-triviality-via-rank-four-cuntz-family`
    requires, is stated only for `L_(F_2)(1,2)`.
- **Positive-root data cannot carry checks (a)-(c) (w4-heisenberg, 2026-09-12).** The `S_i`, `T_j`
  and `e` described above are built from `sigma` on `UT_4(R)`, which is locally finite. Its regular
  rank model has `rk(N_23 N_12) = 3/8`, and it satisfies every relation of `UT_4(R)` (the two associator
  readings of `x_14` included), the ring structure of a rank ultraproduct, and every rank equality
  from isomorphisms of finite subgroups. If `T_i S_j = delta_ij e` and `rk(e) = rk(N_23 N_12)` followed
  from these, the regular model would give idempotents `S_i T_i`, each of rank at least `rk(e) = 3/8`.
  With completeness they are orthogonal and `rk(e) >= 2 rk(e)`. Even without completeness,
  `T_0 S_0 = e = T_1 S_1`, `T_1 S_0 = 0` already make `S_0 T_0`, `S_1 T_1` orthogonal subidempotents of
  `e` of rank at least `rk(e)`. So at least one check must use `sigma` on negative root elements or
  torus units, jointly on a nonsofic subgroup
  (`unitriangular-data-cannot-assemble-corner-leavitt-families`, artifact Section 3).
