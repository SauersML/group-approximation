# Rank-four associativity: decisive plans for the two-root gate

Lane `w3-strategist-gate`, 2026-09-12. Now the lead lane of family R4.

This artifact turns the state of the R family into plans for the rank gate
`rank-models-of-el3-satisfy-the-two-root-identities`. The gate says that `N_23 N_12 = 0` in every
characteristic-`p` rank model of `EL_3(R)`, where `R = L_K(1,2)` and `K` is finite. Closing the gate in
either direction settles `leavitt-el3-rank-models-over-finite-fields-are-trivial`, and with it
`non-linear-sofic-group`.

**Lead pass (family R4).** Section L and the passages marked *(lead)* replace the first landing
(5b46fe59c5). In short:
* **Mechanism dies.** The mechanism listed for Plan 1 fails, because all of its relations lie in
  `U_4(R)` (L7).
* **Index-3 placement fails.** The placement the orth lane fixed holds only modulo block-support defects
  (L3).
* **Route survives.** The route is still valid, and it is equivalent to the gate.
* **Endpoint.** Completeness is not needed, and approximate relations suffice (L1).
* **Calibration corrected.** An exact family inside `F_2[R^x]` would give a Gottschalk counterexample. It
  would not be an absurdity (L4a, corrected by w4-vf-gate).
* **Two live questions.** An operation that lowers the defect by a fixed factor (L5), and rank models
  over Cohn coefficients (L8).

Commit hashes below are the ones reported by the landing lanes. Node ids are the stable references.

## The opening the finished lanes leave

Two established results frame the problem.
* By `leavitt-isometry-commutators-constrain-el3-rank-models`, the gate amounts to assembling an order-two
  Leavitt family in a corner.
* By `scalar-two-root-rank-data-cannot-force-the-identity`, rank values alone do not suffice.

By Khanh--Thanh, `R^x = EL_n(R)` for every `n >= 2` (`leavitt-gl-equals-el-and-perfect-unit-group`), so
every model of `R^x` is also a model of `EL_4(R)`. *(lead)* This adds coordinates, not relations. The
first landing claimed that the rank-3 analysis "cannot see" these identities. That claim was wrong.

## Plan 1: the four-index Cuntz assembly

Node `rank-four-isometry-relations-give-corner-cuntz-family`, route
`leavitt-el3-triviality-via-rank-four-cuntz-family`.

**Claim.** If the block defect `D` is nonzero, then some nonzero corner holds an order-two Leavitt family.
Such a family is excluded (L1). So `D = 0`, and the model is trivial.

*(lead)* **The listed mechanism dies (L7).** The fixed placement is circular (L3).

## Plan 2: the Heisenberg centre pairing

Node `heisenberg-centre-pairing-constrains-two-root-defect`.

*(lead)* **Dead as written (L7).**

## Plan 3: the algebra dichotomy

Node `leavitt-unit-linear-soficity-is-ring-rank-approximability`.

*(lead)* **Collapsed.** w4-r4-approx (b7b0e9d387, 9930bb89f5) shows that the right-hand side is false:
every unital map `L_K(1,d) -> M_n(k)` has a multiplicativity defect of at least `1/3` on one of three
pairs. Moreover `rk(1 - st) = rk(1 - ts)` exactly. So the node only restates "`R^x` is not `F_p`-linear
sofic".

## Ranking (lead pass)

1. The live questions of L5 and L8, under the constraints of L4 and L7.
2. The Plan 1 route: valid and equivalent to the gate. Its mechanism and placement are dead.
3. Plans 2 and 3: dead or collapsed.

## L. Lead integration (family R4)

### L1. Target: approximate relations in one corner

**Canonical endpoint.** `toeplitz-isometry-defects-have-total-rank-at-least-one` (w4-r4-approx). For every
Sylvester matrix rank function, and all `S_0, S_1, T_0, T_1` in `eAe`,

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0) .
```

**Exact form.** `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple` (w4-r4-corner, 5d14c96d85).
w4-r4-complete retired its own duplicate (b09f639b5d).

**Verification.** w4-vf-gate: PASS, with three independent derivations agreeing (e4d7e1c7fa).

**Consequences.**
* Check (ii) is not needed.
* It is enough to give definitions whose three defects sum to less than `rk(e)` at a single finite stage.

### L2. Logical status

The claim's conclusion is impossible in every rank ultraproduct. So, given the established nodes, the
claim is equivalent to the gate. For exact relations, positivity of `e` comes for free (w4-r4-corner).
All the weight falls on the construction.

### L3. Candidate placements, and why both are circular

**Baseline.** In `F_2[R^x]`, put `tau(a) = (x_12(a) - 1)(x_21(1) - 1)`. The linear extension
`pi : F_2[R^x] -> M_3(R)` sends `tau(a)` to `a E_11`. The resulting candidate is the matrix-unit
extraction. Every relation it needs is `sigma` of a nonzero element of `ker pi`, and forcing those
elements to vanish is the gate itself. (Verifier: PASS.)

**Index-3 placement.** w4-r4-orth (fcffe16327), `index-three-corner-placement-holds-only-modulo-two-root-defects`.
* **Definition.** `S(b) = n_31(b) n_13(1)` and `T(a) = n_34(a) n_43(1)`. Let `e` be the range idempotent
  of `n_31(1) n_13(1)`, and put `S_j = e S(s_j) e`, `T_i = e T(t_i) e`. In honest models this is the
  index-3 corner family, with `e = E_33`.
* **Exact identity.**
  `T(a) S(b) = n_31(ab) W n_13(1) + Delta_row + Delta_rev`, where
  `W = X_41(b) X_34(a) X_31(b) X_43(1)`, `Delta_row` carries the same-row product `n_31(b) n_34(a)`, and
  `Delta_rev` carries the reversed product `n_41(b) n_34(a)`.
* **Verdict.** Both deviation terms are block-support failures in `ker pi`, so the placement has the L3
  shape. Replacing index 4 by index 2 gives the same identity inside `EL_3`, so the fourth index adds
  nothing here. The cross term `T(t_1) S(s_0)` is nonzero in the regular representation of `SL_8(F_2)`,
  so the joint Leavitt relations must enter.
* **Consequence.** Check (i) fails for both admissible placements.

### L4. Calibrations

**(a) Kaplansky and Gottschalk (corrected by w4-vf-gate, §1.8 of `gk-vf-gate-verification-2026-09-12.md`).**
* Suppose the three relations of L1 held, with `e != 0`, inside `F_2[R^x]` itself. Then `F_2[R^x]` would
  not be directly finite. That refutes Kaplansky's direct finiteness conjecture for `R^x` in characteristic
  two.
* Through `nonsurjunctive-from-stable-finiteness-failure`, this gives a **Gottschalk counterexample**. That
  is a payoff, not an absurdity.
* The first version said instead that Elek--Szabo would make `R^x` non-sofic. That adds nothing, because
  `R^x` is already nonsofic on main (`openai-leavitt-unit-nonsofic`).
* So this is a marker for an outcome, not a firewall. The constraint applies to (i) and (iii) jointly:
  (i) may be ring identities, provided that `e != 0` is certified through the rank on `M`.

**(b) Test bed.** Theorem 3 of `el3-two-root-self-similarity-2026-09-12.md` gives models with
`rk(N_23 N_12) = 2/9` over coefficient rings that have rank models. If a proof of positivity uses only
Steinberg relations and rank, the chosen `e` must have positive rank in those models.

### L5. Defect gap established; the descent cannot finish

w4-gate-descent: `leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`,
`nested-two-root-defect-pieces-decay-geometrically-both-ways`,
`near-minimal-defect-models-have-multiplicative-cylinder-defects`, and the artifact
`two-root-defect-descent-gap-2026-09-12.md`.

* **Gap.** There is a constant `c_0 > 0` with `c_0 rk(1-f) <= rk((1-f) D_A) <= rk(1-f)/2`, where `fM` is
  the fixed right ideal of `sigma(R^x)`. The constant `c_0` is not explicit.
* **Descent.** For disjoint cylinders, `c_* f(k) <= f(k+1) <= f(k)/2`. The pieces at least halve at every
  step, so there is no limit corner, and the finish the first version proposed has nothing to act on.
* **Commits reported by the lane.** Gap e24abed257; descent and near-minimal models 3116be756a; open
  target 015be9163a.
* **Live question.** Open node `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, with route
  `leavitt-rank-triviality-via-strict-defect-submultiplicativity` into `non-linear-sofic-group`. Find an
  operation on fixed-point-free models that lowers the normalized defect by a fixed factor. The natural
  source, per w4-gate-descent, is the halving relation
  `iota_A(x_12(1)) = (1 + S[A00]T[A100])(1 + S[A01]T[A101])`. It gives
  `D_A = (1+b+d)X + (1+a+c)Y + XY + cb + da`, where `X` and `Y` are the child defects. No bound has been
  extracted yet.
  * Strict submultiplicativity would suffice: `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1`.
  * Honest tensor configurations attain `theta = 1`, so a proof must use the Leavitt relations.
  * By L7, it must also use units outside `iota_A(U_3) x iota_B(U_3)`. w4-r4-orth has been redirected here.

### L6. Status

| item | lane | status |
|---|---|---|
| (i) three relations | w4-r4-orth | placement fixed and circular (L3); redirected to L5 |
| (ii) completeness | w4-r4-complete | not needed. Transport formula `leavitt-completeness-transport-formula-for-root-data` established and firewalled (it lives in `U_3(R)`). Opened L8 (b09f639b5d) |
| (iii) positivity | w4-r4-corner | free for exact relations; for w4-r4-orth's placement, established in characteristic two by `opposite-unit-root-product-vanishes-only-for-trivial-models` (ef454c9283; lead spot-check of the braid step passes); only the L3 deviation terms remain open; route framing merged (b0d955566e) |
| endpoint | w4-r4-approx | canonical form established; verifier PASS |
| block to whole group | w4-r4-corner | `el4-model-trivial-on-one-unit-root-element-is-trivial`; verifier PASS; required by the route |
| odd characteristic | w4-r4-adversary | `reversed-root-pair-identity-forces-root-squares-to-vanish` (9fd9898e8e); verifier PASS; used by the route |
| break the plan | w4-r4-adversary | mechanism dies (c6697aa47b; L7) |
| approximability node | w4-r4-approx | collapsed |
| Heisenberg node | w4-heisenberg | dead; firewall landed (f576dccf26); finished |
| defect gap and descent | w4-gate-descent | Established, verifier PASS: gap, two-sided descent, near-minimal multiplicativity. Open target: `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, with route `leavitt-rank-triviality-via-strict-defect-submultiplicativity` into `non-linear-sofic-group`. Lead spot-check of the route passes: `f(2) >= c_* delta >= delta^2/(1+eps)` contradicts `theta delta^2` once `eps < 1/theta - 1` |
| verification | w4-vf-gate | Record: `gk-vf-gate-verification-2026-09-12.md`, Sections 1--9. PASS on every established family node: endpoint, block triviality, reversed root, both firewalls, index-3 placement, completeness transport, defect gap, descent, near-minimal models, opposite-root positivity, approximability collapse. Corrections folded in: L4a, frames, odd characteristic. Plan 2 stays open with two overstatements (§1.7). No decision-level verdict |

### L7. The listed mechanism dies

**Abelian model.** w4-r4-adversary (c6697aa47b), `unipotent-frame-relations-cannot-assemble-corner-cuntz-family`.
* `g -> u^phi(g_12) v^phi(g_23)` on `F_p[C_p^2]` is a homomorphism of `U_4(R)`.
* It satisfies every listed relation.
* It has `rk(N_23 N_12) = (p-1)^2/p^2` and zero `x_14` data.
* Lead spot-check: pass.

**Locally finite firewall.** w4-heisenberg (f576dccf26), `unitriangular-data-cannot-assemble-corner-leavitt-families`.
* `UT_4(R)` is locally finite.
* Its regular rank model satisfies every `UT_4` relation and every rank that is invariant under
  conjugation.
* It has `rk(N_23 N_12) = 3/8`.

**Consequences.**
* A proof must use `sigma` on opposite root, Weyl or torus elements, jointly on a nonsofic subgroup,
  together with the rank of `M`.
* The Heisenberg plan dies the same way on `U_3(R)`.

### L8. Cohn coefficients (w4-r4-complete, open)

The node is `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`. It asks whether
`N_23 N_12 = 0` in every rank model of `EL_3(C)`, where `C` is the Cohn algebra `t_i s_j = delta_ij`,
without completeness.
* **`C` has no unital rank model.** `T_0 S_0 = 1` forces `S_0 T_0 = 1`, so `T_1 = 0`.
* **Pullback.** `R` is a quotient of `C`, and `EL_3(C) -> EL_3(R)` is onto. So every rank model of
  `EL_3(R)` pulls back to a rank model of `EL_3(C)` with the same `D`.
* **If the node is true,** it gives the binary gate.
* **If it is false,** completeness must enter any construction. It cannot enter through root data, since
  the transport formula lives in `U_3(R)`. It has to enter through units outside `U_4(R)`.
