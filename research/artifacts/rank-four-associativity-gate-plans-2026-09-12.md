# Rank-four associativity: decisive plans for the two-root gate

Lane `w3-strategist-gate`, 2026-09-12, now lead lane of family R4. This synthesizes the R-family
state into plans for the rank gate `rank-models-of-el3-satisfy-the-two-root-identities`: the claim
that `N_23 N_12 = 0` for every characteristic-`p` rank model of `EL_3(R)`, where `R = L_K(1,2)` and
`K` is finite. Closing the gate in either direction settles
`leavitt-el3-rank-models-over-finite-fields-are-trivial`, and hence `non-linear-sofic-group`.

**Lead pass (family R4).** Section L and the passages marked *(lead)* supersede the first landing
(5b46fe59c5). In short:
* the plan node is equivalent to the gate, and its construction was never defined;
* completeness is not needed, and approximate relations suffice (L1, via w4-r4-approx);
* a Kaplansky calibration forces any construction to use the regularity or rank of `M` (L4a);
* the approximability node collapses to the target (w4-r4-approx, established).

## The opening the finished lanes leave

* `leavitt-isometry-commutators-constrain-el3-rank-models` shows that the gate is exactly the
  assembly of an order-two Leavitt family in a corner `eMe`. Assembling that family in a single
  Peirce corner is circular.
* `scalar-two-root-rank-data-cannot-force-the-identity` shows that rank values never suffice.
  Operator identities are needed.

By Khanh--Thanh, `R^x = GL_n(R) = EL_n(R)` for every `n >= 2`
(`leavitt-gl-equals-el-and-perfect-unit-group`). So a rank model `sigma : R^x -> M^x` is at the same
time a homomorphism `EL_4(R) -> M^x`, with no extension step. There are two readings of
`x_14(abc)`:
* `[x_13(ab), x_34(c)]`, with `x_13(ab) = [x_12(a), x_23(b)]`;
* `[x_12(a), x_24(bc)]`, with `x_24(bc) = [x_23(b), x_34(c)]`.

Equating them gives an operator identity.

*(lead)* This adds no relation. `EL_4(R)` and `EL_3(R)` are the same group `R^x`, so every `EL_4`
Steinberg relation is already a relation of `EL_3(R)`. What the fourth index adds is coordinates:
root pairs whose products are not confined to one Peirce corner of the unit `EL_3` pair. The first
landing said the rank-3 analysis "cannot see" these identities, and that was wrong.

## Plan 1: the four-index Cuntz assembly

Node `rank-four-isometry-relations-give-corner-cuntz-family`, route
`leavitt-el3-triviality-via-rank-four-cuntz-family`.

**Claim.** Let `sigma` be a char-`p` rank model of `R^x`, read as a model of `EL_4(R)`. If
`D = N_23 N_12 != 0`, then there is an idempotent `e` of positive rank, and there are `S_i, T_j` in
`eMe` satisfying the Cuntz relations.

**Why it would close the gate.** Such a family is excluded (L1). So `D = 0`, and then
`el3-unit-root-matrix-units-iff-two-root-identities` and
`matrix-unit-rank-models-extract-ring-rank-models` give triviality.

**Why the verified obstructions miss it.**
* It works with operators, not rank values. *(lead)* This is true only if the construction uses the
  regularity or rank of `M` at an intermediate step (L4a).
* It uses the Leavitt relations, which is the input demanded by
  `fd-represented-coefficients-violate-two-root-identities`.
* It invokes neither property (T) nor rounding.

**First lemma.** The isometry commutators hold on two root pairs of `EL_4(R)`:
`[x_12(t_i), x_23(s_j)] = x_13(delta_ij)` and `[x_23(t_i), x_34(s_j)] = x_24(delta_ij)`. The cross
frame ties the two pairs together through index 3.

*(lead)* The first landing said that the telescoping "is now a Steinberg identity". That was never
shown, and by L4a it cannot be an identity in the group algebra. `S_j`, `T_i` and `e` are still
undefined (L3).

## Plan 2: the Heisenberg centre pairing

Node `heisenberg-centre-pairing-constrains-two-root-defect`. The commutator pairing
`beta(a,b) = n_13(ab)` takes values in a bounded-rank, abelian, square-zero group, and it is onto `R`
because `1 = s_0 t_0 + s_1 t_1`. Plan: turn this tension into an infinite orthogonal chain unless
`D = 0`. It is not yet a contradiction, because the cross term of the branch split is not
controlled.

## Plan 3: the algebra dichotomy

Node `leavitt-unit-linear-soficity-is-ring-rank-approximability`.

*(lead)* **Collapsed.** w4-r4-approx
(`research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md`) proves that the
right-hand side is false. Any unital map `L_K(1,d) -> M_n(k)` has normalized multiplicativity defect
at least `1/3` on one of the pairs `(t_0,s_0)`, `(t_1,s_1)`, `(t_1,s_0)`. Moreover
`rk(1 - st) = rk(1 - ts)` exactly, so isometries are never approximately proper. The node therefore
restates "`R^x` is not `F_p`-linear sofic": its backward direction is vacuous and its forward
direction is the gate.

## Ranking

1. Plan 1 is the family target, with L1--L4 as its interface.
2. Plan 3 is collapsed: it restates the target.
3. Plan 2 is independent but not yet a contradiction.

## L. Lead integration (family R4)

### L1. Target: approximate relations in one corner

**Quantitative endpoint** (w4-r4-approx, `toeplitz-isometry-defects-have-total-rank-at-least-one`).
For any Sylvester matrix rank function, an idempotent `e`, and `S_0, S_1, T_0, T_1` in `eAe`:

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0) .
```

Lead spot-check, pass: `X = X(e - ST) + (XS)T` together with the block elimination
`rk(e - ST) = rk(e - TS)`. So the route needs neither completeness nor `T_0 S_1 = 0`, and
**check (ii) is not needed**. The relations also need not be exact. Definitions of `S_i`, `T_j`,
`e` whose three defects sum to less than `rk(e)` already contradict the existence of the model, at a
single finite stage.

### L2. Logical status

Given the established nodes, "`D != 0` implies such a family" is equivalent to "`D = 0` always",
which is the gate. The plan node has no content beyond a construction. Check (iii), a positive
lower bound on `rk(e)` exceeding the defects, carries the full weight.

### L3. The baseline candidate, and why it is circular

In `F_2[R^x]`, put `tau(a) = (x_12(a) - 1)(x_21(1) - 1)`. Let `pi : F_2[R^x] -> M_3(R)` extend
`R^x = GL_3(R)` linearly, so that `pi(tau(a)) = a E_11`. Extend `sigma` linearly as well.

The candidate `T_i = sigma(tau(t_i))`, `S_j = sigma(tau(s_j))`, `e = N_12 N_21` is the matrix-unit
extraction. Each relation it must satisfy is `sigma` of a nonzero element of `ker pi`. The regular
representation does not kill such an element, so group relations never force its image to vanish;
forcing that is the gate itself. Theorem 3 of `el3-two-root-self-similarity-2026-09-12.md` shows the
forcing fails over rank-modelled coefficients.

A four-index candidate has to replace `tau`, and none has been defined yet. **Open task
(w4-r4-orth): fix one definition of `S_j`, `T_i` and `e`, so that (i) and (iii) are checked on the
same objects.**

### L4. Two calibrations every construction must pass

**(a) Kaplansky calibration.** Suppose the three relations of L1 held, with `e != 0`, for elements of
the group algebra `F_2[R^x]` itself. Then `(T_0 + 1 - e)(S_0 + 1 - e) = 1` while
`(S_0 + 1 - e)(T_0 + 1 - e) != 1`, so `F_2[R^x]` is not directly finite. That refutes Kaplansky's
direct finiteness conjecture in characteristic two and, by Elek--Szabo, makes `R^x` non-sofic. This
is far stronger than the gate and is not expected. So check (i) must use the regularity or the rank
function of `M` at some intermediate step, for instance range idempotents `q` with `PM = qM` as in
`leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`.

**(b) Test bed for (iii).** Theorem 3 of the self-similarity artifact gives, over any coefficient ring
with a unital rank model, models with `rk(N_23 N_12) = 2/9`. If a proof of (iii) uses only
Steinberg relations and rank, it applies to these models, so the chosen `e` must have positive rank
there. That is a paper check for w4-r4-corner and w4-r4-adversary. If `e = 0` in these models, the
proof of (iii) must also use the Leavitt relations.

### L5. Folding w4-gate-descent

w4-gate-descent works on the nested defect pieces `q_k` of w3-gate-bridge-b (b62a0dc006), with
`delta_k = rk(q_k)`. Its aim is a uniform bound `delta_(k+1) >= c delta_k`, which together with
`R ~= R^2` gives approximately multiplicative unital maps `phi_k : R -> q_k M q_k`.

*Finish, sharpened by L1.* Suppose that at one stage the defects of `phi_k` on `(t_0,s_0)`,
`(t_1,s_1)` and `(t_1,s_0)` sum to less than `delta_k`. Then L1 with `e = q_k` is a contradiction.
No ultraproduct over `k` is needed.

*Caveat.* Errors are measured in absolute rank against `delta_k`, which can decay geometrically. So
absolute errors that are merely `o(1)` do not suffice. The route uses rank, so L4a does not apply.
Its test bed is the Toeplitz group calibration (6ebb4155b8).

### L6. Status

| item | lane | status |
|---|---|---|
| (i) three relations of L1, approximate | w4-r4-orth | open; define `S_j`, `T_i`, `e` first (L3); L4a applies |
| (ii) completeness | w4-r4-complete | not needed for the route (L1) |
| (iii) `rk(e)` above the defects | w4-r4-corner | open; carries the whole gate (L2); test bed L4b |
| break the plan | w4-r4-adversary | L4a, L4b |
| approximability node | w4-r4-approx | collapsed; endpoint established (4ff43a9370, 257eb0d4b1, 653264b752); verification requested |
| Heisenberg node | w4-heisenberg | open |
| relative descent bound | w4-gate-descent | open; finish and caveat in L5 |
| verification | w4-vf-gate | none landed yet |
