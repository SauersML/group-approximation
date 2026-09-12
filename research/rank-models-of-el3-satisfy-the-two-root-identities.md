---
rg: 2
id: rank-models-of-el3-satisfy-the-two-root-identities
kind: claim
title: Every rank model of EL_3 over a simple algebra with no rank model satisfies N_12^2 = 0 and N_23 N_12 = 0
distinct_from:
  el3-rank-models-factor-through-ring-rank-models: that asserts every such model is trivial; this asserts two product identities among the six unit root unipotents. The two are equivalent through the routes two-root-identities-give-el3-ring-rigidity and el3-ring-rigidity-gives-the-two-root-identities, which form an intended cycle.
  el3-unit-root-matrix-units-iff-two-root-identities: that is the established equivalence between the identities and the matrix-unit hypothesis for any single model; this is the open assertion that every rank model over the gate's coefficient rings satisfies them.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

**OPEN.** Let `p` be a prime and `R` a simple unital algebra over a field of characteristic
`p` with no unital ring homomorphism into any rank ultraproduct over a field of characteristic
`p`. Let `M` be such a rank ultraproduct and `sigma : EL_3(R) -> M^x` a homomorphism, and put
`N_ab = sigma(x_ab(1)) - 1`. Then

```text
N_12^2 = 0        and        N_23 N_12 = 0 .
```

In characteristic two the first identity is automatic. For `R = L_(F_2)(1,2)` this is the
single identity `(x_23(1) - 1)(x_12(1) - 1) = 0` in every characteristic-two rank model of the
Leavitt unit group. It is equivalent to `el3-rank-models-factor-through-ring-rank-models`, whose
payoff is `non-linear-sofic-group`.

## Attempts

- **Reduction: landed (gk-rk-unipotent, 2026-09-12).**
  - `el3-unit-root-matrix-units-iff-two-root-identities`: the identities are exactly the
    matrix-unit hypothesis.
  - `matrix-unit-rank-models-extract-ring-rank-models`: matrix-unit models extract a ring rank
    model, or are trivial.
  - So this claim and the gate claim are equivalent (artifact Section 3).
- **Group relations over finitely represented coefficients cannot prove it.**
  `fd-represented-coefficients-violate-two-root-identities` gives honest regular-representation
  models of `EL_3(S)` with `N_23 N_12 != 0` whenever `S` maps into some `M_n(F_p)`. That covers
  the Toeplitz subring `<s_0, t_0 | t_0 s_0 = 1>`. `gk-l-gate-pos`'s natural tensor dual model
  of `EL_3(F_2[t])` also violates the identity. A proof must use coefficients generating a
  subring with no finite-dimensional representation, such as a unital Leavitt family, or the
  no-rank-model hypothesis beyond relations.
- **Five-term expansion: dies.** `N_13 = XY + YX + XYX + YXY + XYXY` with `X = N_12`,
  `Y = N_23` (characteristic two). No Steinberg relation among the unit root elements isolates
  `YX`.
- **Self-similar displacement counting: dies.** On `SL_3(F_2)` the model is the diagonal
  restriction of the commuting pair `(sigma iota_0, sigma iota_1)`. Equal displacement of
  `(x,1)`, `(1,x)` and `(x,x)` forces free-type or trivial behavior on outer tensor components,
  and free-type components violate the identity. Modules that are not outer tensor products
  escape, so uniform displacement does not force the identity (artifact Section 5).
- **Same-row and same-column identities first: dies.** From the squares, `N_12 N_13 = 0` and
  `N_12 N_32 = 0` leave the residual `N_12 N_21 N_32 (1 + N_21)`, which they do not force.
- **Isometry commutator relations: new handle, not yet connected (gk-ri-nofd, 2026-09-12).**
  `leavitt-isometry-commutators-constrain-el3-rank-models` records, from `t_i s_j = delta_ij`,
  the reversed identities on `A_i = n_12(t_i)`, `B_j = n_23(s_j)`:
  `i != j` gives `A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j = 0`, and `i = j` gives
  the same expression equal to `n_13(1)`. These use coefficients with no finite-dimensional
  representation, the input required by `fd-represented-coefficients-violate-two-root-identities`,
  and were unused by the dead attempts. Open bridge: the target `N_23 N_12` carries coefficient
  `1`; `1 = e_0 + e_1` with `e_i = s_i t_i` gives
  `1 + N_12 = (1+n_12(e_0))(1+n_12(e_1))`, but `1` is not an additive combination of the `t_i`
  and `x_12` of a product is not a commutator, so no group-relational bridge is known.
- **Extraction is a corner Leavitt family; single-corner route circular (gk-ri-nofd).** A unital
  `R -> eMe` is an order-two Leavitt family in the corner `eMe`; by [TR] Theorem D that corner is
  a rank ultraproduct, so `leavitt-algebra-has-no-unital-rank-model` already forbids it
  (impossibility half established). Telescoping the four partial isometries in one Peirce corner
  needs the block form, i.e. `N_23 N_12 = 0`, so that route assumes its conclusion. A
  non-circular assembly of the four partial isometries from a model with `N_23 N_12 != 0` is the
  open content. Artifact `research/artifacts/leavitt-isometry-commutator-relations-2026-09-12.md`.
- **Simultaneous conjugacy of the shifted pair: dies (gk-rk-unipotent, 2026-09-12).**
  `shifted-root-pair-conjugates-to-idempotent-root-pair`: `(x_12(t_0), x_23(s_0))` has the same
  commutator `x_13(1)` as the unit pair but is not conjugate to it. The invariant
  `(ker N ∩ ker M) / (… ∩ (Im N + Im M))` is `0` for the unit pair and `s_1 R` for the shifted
  pair. The shifted pair is conjugate to `(x_12(e_0), x_23(e_0))` by an explicit `g`, which gives
  only `rk(n_23(s_0) n_12(t_0)) = rk(n_23(e_0) n_12(e_0))` (artifact Section 6.1).
- **Orthogonal splitting: dies.** With `a' = sigma(x_12(e_0))`, `a'' = sigma(x_12(e_1))` and
  similarly for `b`, `YX = Y'X' b''a'' + b'' X''Y' + X' Y''a'' + Y''X''`. No term is forced to vanish
  outside block models. It lives in the finite group `SL_3(F_2)^2` (artifact Section 6.2).
- **Every finite-subgroup mechanism: dies, by calibration.**
  `finite-subgroup-rank-data-cannot-force-two-root-identity`: the free profile
  `r_K = rank lambda_K / |K|` on all finite subgroups respects restriction and every conjugacy,
  and has `rk(N_23 N_12) = 3/8`. So relations inside finite subgroups, conjugacy between finite
  subgroups and per-subgroup ranks cannot force the identity. That covers:
  - Steinberg relations with any coefficients, the isometry commutator identities, and the
    splitting through `e_0`, `e_1`;
  - branch expansions under involutive `diag(w,w,w)`;
  - Leavitt and Thompson conjugacy, and level-group counting;
  - even `(x_12(t_0), x_21(s_0))`, which generates `S_3`.
  A proof must use `sigma` on a subgroup not contained in any finite subgroup, for example
  `<diag(u, u^-1, 1), x_12(1)>` with `u` of infinite order, or joint ranks across finite subgroups
  generating an infinite group (artifact Section 6.3).
- **Uniform self-similar tower: dies (gk-ri-selfsim, 2026-09-12).**
  - `rank-modelled-coefficients-violate-two-root-identities` (1ce1d7bd6a): any unital coefficient
    ring with a unital rank model has a natural tensor-square model of `EL_3` with
    `rk(N_23 N_12) = 2/9`.
  - The dyadic constants `D = colim M_(2^k)(F_2)` carry every uniform self-similar relation:
    `iota_0`, `iota_1`, `diag(w,w,w)`, `x_ab(1) = iota_0(x_ab(1)) iota_1(x_ab(1))`, and the constant
    block coordinates. They have such a model, so
    `dyadic-constant-el3-rank-models-satisfy-two-root-identity` is refuted and
    `two-root-identity-by-restriction-to-dyadic-constants` is dead.
  - "No finite-dimensional representation" is not enough. A proof needs relations whose
    coefficient subring has no unital rank model, and `D` together with `s_0, t_0` already
    generates `L_(F_2)(1,2)`.
- **Branch split: exact, but an upper bound only (gk-ri-selfsim).**
  `el3-two-root-violation-splits-over-leavitt-branches` gives
  `N_23 N_12 = P_0(1+a_1+b_1+P_1) + P_1(1+a_0+b_0) + (b_0 a_1 + b_1 a_0)`, where the branch
  products `P_i` are conjugate by `sigma(diag(w,w,w))`. It also gives the defect factorization
  `n_13(ab) = XY + (1+X)(YX)(1+Y)`. This bounds `rk(N_23 N_12)` above by branch and cross terms;
  tensor-type branches give no lower bound.
  - Open next unit: a contracting bridge from `delta(1,1)` to `delta(t_i, s_i)`. The factorization
    gives `rk(N_12 N_23 - n_12(t_i) n_23(s_i)) <= delta(1,1) + delta(t_i, s_i)`.
- **Sofic subgroups: die, by calibration (gk-rk-unipotent, 2026-09-12).**
  `sofic-subgroups-carry-rank-models-violating-two-root-identity`: every sofic subgroup of
  `EL_3(R)` containing `x_12(1)` and `x_23(1)` has a rank model, from its sofic approximation,
  which is free on `D_8`, so `rk(N_23 N_12) = 3/8`. Covered: `UT_3(R)` and its torus extensions,
  `EL_3(A_inf)`, and residually finite Kazhdan subgroups such as `EL_3(F_2[s_0])`. A proof must
  use `sigma` jointly on a nonsofic subgroup containing both root elements, and would prove that
  subgroup nonsofic (artifact Section 6.4).
- **Corner locality, and the nine-leaf mechanism aimed at the identity (gk-gate-nonsofic, 2026-09-12).**
  - `two-root-identity-is-corner-local-for-leavitt-rank-models` (e5f2fbc35f), established: for
    a char-2 rank model `sigma` of `R^x`, `sigma` trivial ⟺ the identity holds on the unit pair ⟺
    it holds on `iota_P(unit pair)` for any single cylinder `P`. Through
    `shifted-root-pair-conjugates-to-idempotent-root-pair`, it is also equivalent to
    `rk(n_23(s_0) n_12(t_0)) = 0`. So the pair may sit inside `C_G(Gamma)` for the nine-leaf `Gamma`.
  - Audit (artifact `research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md`,
    Section 3), with `x', y'` on `[1000]`:
    - The defect piece `Q = im(N_23' N_12')` is almost invariant under `sigma(Gamma)`, not fixed.
    - Globality `leavitt-rank-models-kazhdan-fixed-ideals-are-global` rounds only fixed ideals.
    - Single-piece rounding is refuted for Kazhdan groups over finite fields (the half-degree
      truncation in `kazhdan-group-rank-models-admit-no-expander-decomposition`).
    - `<Gamma, x', y', u>` contains `Gamma` and is nonsofic, so the calibrations do not pre-empt the
      argument. It dies at (K).
  - A rescue must use data that counterexample lacks: the compression relation with property (T) of
    the compressor group, the absence of finite-dimensional representations of `R^x`, or the global
    fixed-ideal condition.
- **Compressor conjugation: exact, but rank-preserving (gk-gate-compress, 2026-09-12).**
  - `compressors-conjugate-leak-free-root-pairs`: explicit units c, c' give
    `(x_12(a), x_23(b' t_1 t_1)) ~ (x_12(s_0 a t_0), x_23(s_0 b'))` and
    `(x_12(s_1 s_1 a''), x_23(b)) ~ (x_12(a'' t_0), x_23(s_0 b t_0))`. The leak-free coefficient sets
    are exactly `R t_1 t_1` and `s_1 s_1 R`; elsewhere the conjugates leak into `x_21`, `x_32` and the
    torus. (The first landing said `s_1 R` for the `c'` half; `gk-vf-linear` Section 48 found that
    false, and the claim and artifact are corrected forward.)
  - `scalar-two-root-rank-data-cannot-force-the-identity`: unit and compressor moves never meet the
    unit pair, and the Cuntz decomposition gives only subadditive upper bounds. The Boolean function
    `eps [a != 0][b != 0]` satisfies conjugation invariance and root subadditivity, so no bridge on
    delta-values can prove this claim.
  - Where it dies: compression never shrinks rank. A proof needs a lower bound from orthogonality, or
    operator identities beyond rank data (artifact
    `research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md`).
- Lane `w3-gate-bridge-b` (input (ii), no finite-dimensional representations; artifact
  `research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md`):
  - `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`. In a nontrivial model, the
    defect piece of the `[1000]` corner pair is never fixed by the nine-leaf `Gamma`. `Gamma` acts on
    it by an injective rank model of `R^x`, whose corner products compress nontrivially onto the
    piece, and a compressor carrying the pair into `Gamma` has `q sigma(u) q != 0`. So globality
    (degree `(1,0)`) is already used in full. The invariant case reproduces the problem on nested
    corners with weakly decreasing ranks.
  - `kazhdan-groups-without-fd-reps-violate-two-root-identity`. `EL_3(C(X,F_2) x| Z)` over the
    period-doubling Toeplitz subshift is finitely generated, Kazhdan, and has no finite-dimensional
    representation. Yet it has a violating rank model (`rk = 2/9`), a diffuse relative commutant,
    and a defect piece fixed by a Kazhdan centralizer. So absence of finite-dimensional
    representations, even with (T), forces nothing.
  - Where it dies: no uniform bound `delta_(k+1) >= c · delta_k` on the nested defect pieces, and no
    ring map from `R` into a defect corner built from the restricted model. A proof must use that
    `R` has no rank model, or the compression relation.
- **Characteristic three, ternary Leavitt units** (w3-gate-char3, artifact
  `research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`).
  - **The gate.** For `R = L_(F_3)(1,2)` the gate is the single claim
    `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`. A model moving `z = −1`, an injective
    model, an anti-central model, and a nontrivial model of `R^x/{±1}` all exist together
    (`ternary-leavitt-rank-models-move-z-iff-nontrivial`).
  - **Corner locality.** It holds with perfection plus simplicity modulo scalars in place of simplicity,
    and the extraction needs both odd-characteristic identities.
  - **Torus normal form.** `N_12 = A − A^2` with `A` flipping torus weights, so the first identity is
    `A^2 = 0` (`ternary-rank-model-root-element-torus-normal-form`).
  - **Haar law.** Anti-central models carry Haar measure on the signed diagonal
    (`anti-central-rank-models-see-haar-measure-on-signed-diagonal`). Projective content of level groups
    satisfies that law and violates `A^2 = 0`.
  - **Where it dies.** Same place as in characteristic two: relations whose coefficients are
    measure-changing partial isometries, not code-level constants.
- **One identity decides in every characteristic (w4-r4-adversary, 9fd9898e8e).**
  `reversed-root-pair-identity-forces-root-squares-to-vanish`: for any homomorphism
  `sigma : EL_3(R) -> M^x`, `N_23 N_12 = 0` forces `N_ab^2 = 0` for every root.
  - **Proof.** Weyl symmetry spreads the reversed pair to `N_jk N_ij = 0`. Then
    `N_ik = N_ij N_jk X^-1 Y^-1` and `Y^-1 N_ij = N_ij`, so `N_ik^2 = 0`.
  - **Consequence.** The first identity is redundant in odd characteristic too. That includes the
    characteristic-three extraction, which the entry above records as needing both identities.
- **Unitriangular relations: die (w4-r4-adversary, c6697aa47b).**
  - **Which plans.** Plan 1's four-index frame and Plan 2's centre pairing use only relations of
    `U_4(R)`.
  - **Why they die.** `U_4(R)` has an explicit model with `rk(N_23 N_12) = (p-1)^2/p^2` in every
    characteristic (`unipotent-frame-relations-cannot-assemble-corner-cuntz-family`).
  - **What escapes.** One opposite unit root element already generates a copy of `R^x`.
