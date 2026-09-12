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
  `T_0 S_0 = e = T_1 S_1`, `T_1 S_0 = 0` already make `S_0 T_0`, `S_1 T_1` idempotents in `eMe`, each of rank at least `rk(e)`, with `S_1 T_1 S_0 T_0 = 0`. Then
  `S_0 T_0 (e - S_1 T_1)` and `S_1 T_1` are orthogonal idempotents in `eMe`, and `rk(e) >= 2 rk(e)`. So at least one check must use `sigma` on negative root elements or
  torus units, jointly on a nonsofic subgroup
  (`unitriangular-data-cannot-assemble-corner-leavitt-families`, artifact Section 3).
- **Adversarial pass (w4-r4-adversary, c6697aa47b and 9fd9898e8e; artifact
  `research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md`).**
  - **The listed relations live in `U_4(R)`.** Every relation listed above is a relation of the
    unitriangular group `U_4(R)`: both isometry-commutator frames, both readings of `x_14(abc)`, and
    the split of `x_12(1)`.
  - **A model where they hold and the checks fail.** A superdiagonal character `U_4(R) -> F_p^2`,
    acting by translation on `F_p[C_p^2]`, satisfies all of them, with
    `rk(N_23 N_12) = (p-1)^2/p^2` and zero `x_13, x_24, x_14` data. Directly finite corners carry no
    Toeplitz pair. So checks (a)-(c) cannot be derived from unitriangular relations, and in that model
    check (c) fails with `rk(D) > 0` (`unipotent-frame-relations-cannot-assemble-corner-cuntz-family`).
  - **What a proof must use.** `sigma` on something outside `U_4(R)`. One opposite unit root element
    together with `x_IJ(R)` generates `EL_2(R) ~= R^x`, and the torus elements form another copy of
    `R^x`.
  - **Agrees with the lead pass.** The content is the construction, and `EL_4` coordinates add no
    relation. Grouping `{3,4}` through `R^2 ~= R` gives the dictionary in artifact Section 3.
  - **Frame note.** In standard coordinates the block defect `n_23^(4)(1) n_12^(4)(1)` is the
    shifted-pair product `(sigma(x_23(t_0)) - 1)(sigma(x_12(1)) - 1)`, so `D` must be read in the
    block frame throughout. No frame error found in the route.
  - **Odd characteristic.** The route's `D = 0` case needs no second identity, by
    `reversed-root-pair-identity-forces-root-squares-to-vanish`.
  - **Not invalidated.** The claim is equivalent to the defect identity, and the route stays valid.
- **Endpoint, check (c) and framing (w4-r4-corner, 5d14c96d85, 6414c135d1, b0d955566e; artifact
  `rank-four-corner-endpoint-and-framing-2026-09-12.md`).**
  - **Endpoint.** The minimal endpoint agrees with lead pass L1 and with w4-r4-approx. I found it
    independently, with `T_0 S_1 = 0` in place of `T_1 S_0 = 0`, and it is now the established node
    `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple`. The node holds over every field, every `K`
    and every characteristic.
  - **Check (c) needs only `e != 0`.** For `e = 0` every relation holds trivially.
    - `D != 0` makes `sigma` nontrivial, and by the established node
      `el4-model-trivial-on-one-unit-root-element-is-trivial` every `n_IJ(r)` with `r != 0` is then
      nonzero.
    - So any `e` that absorbs `D`, or a nonzero root operator, on one side has `rk(e) > 0`.
    - What check (a) must add is that `S_0` and `T_0` lie in `eMe` for that same `e`. The two
      unitriangular models above show that this is where the non-unitriangular input has to enter.
  - **Drop the literal equality.** `rk(e) = rk(D)` is false in general: the least idempotent with
    `eDe = D` has rank `2 rk(D) - rk(D^2)` (artifact Proposition 2).
  - **Framing.** "`sigma` is at the same time a homomorphism of `EL_4(R)`" holds only through an
    isomorphism `phi_4 : EL_4(R) -> R^x` coming from a four-leaf prefix code.
    - For an `EL_3` model `sigma`, the `EL_3` block of its transport `sigma_4 = sigma ∘ phi_3^-1 ∘ phi_4` is
      `sigma ∘ psi`, with `psi` a non-surjective self-embedding.
    - So `D` is the block defect of `sigma_4`, as the adversarial frame note also says.
    - The route's `D = 0` branch then needs normal closure to pass from "the block is trivial" to
      "`sigma_4` is trivial". The route merge (b0d955566e) adds that node, and the corner-triple node,
      to its requires (artifact §3.2 and §3.4).
  - **Khanh--Thanh fidelity.** The load-bearing input is the Lean theorem `glAll_eq_elementary` on main
    (binary case, every field, no `sorry` in its two files by textual scan). arXiv:2607.10351v1
    (Khanh, Thanh) agrees and is unrefereed; I read pages 1--2 (artifact §3.1).
