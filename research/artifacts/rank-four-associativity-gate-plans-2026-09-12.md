# Rank-four associativity: decisive plans for the two-root gate

Lane `w3-strategist-gate`, 2026-09-12, now lead lane of family R4. Synthesis of the R-family state
into plans for the rank gate `rank-models-of-el3-satisfy-the-two-root-identities`, i.e.
`N_23 N_12 = 0` for every characteristic-`p` rank model of `EL_3(R)`, `R = L_K(1,2)`, `K` finite.
Closing it in either direction settles `leavitt-el3-rank-models-over-finite-fields-are-trivial`
and hence `non-linear-sofic-group`.

**Lead pass (family R4).** Section L and the passages marked *(lead)* supersede the first landing
(5b46fe59c5). In short:
* the plan node is equivalent to the gate, and the first landing never defined its construction;
* completeness is not needed for the contradiction;
* a Kaplansky calibration forces any construction to use the regularity or rank of `M`;
* the approximability node collapses to the target.

## The opening the finished lanes leave

* `leavitt-isometry-commutators-constrain-el3-rank-models` shows the gate is exactly the assembly
  of an order-two Leavitt (Cuntz) family in a corner `eMe`. Assembling it in a **single Peirce
  corner is circular**. A **non-circular assembly** is "the whole gate."
* `scalar-two-root-rank-data-cannot-force-the-identity` shows rank *values* never suffice;
  **operator identities** are required.

The missing room is a fourth index. By Khanh--Thanh, `R^x = GL_n(R) = EL_n(R)` for every `n >= 2`
(`leavitt-gl-equals-el-and-perfect-unit-group`). So a rank model `sigma : R^x -> M^x` is at the
same time a homomorphism `EL_4(R) -> M^x`, with no extension step. The associativity frame is
`[x_12(a), x_23(b)] = x_13(ab)`, `[x_13(ab), x_34(c)] = x_14(abc)`, `x_24(bc) = [x_23(b), x_34(c)]`,
`[x_12(a), x_24(bc)] = x_14(abc)`, and the two readings of `x_14(abc)` give an operator identity.

*(lead)* This adds no relation. `EL_4(R)` and `EL_3(R)` are the same group `R^x`, so every `EL_4`
Steinberg relation is already a relation of `EL_3(R)`. What the fourth index adds is coordinates:
root pairs whose products are not confined to one Peirce corner of the unit `EL_3` pair. (The first
landing said the rank-3 analysis "cannot see" these identities. That was wrong.)

## Plan 1: the four-index Cuntz assembly

Node `rank-four-isometry-relations-give-corner-cuntz-family`, route
`leavitt-el3-triviality-via-rank-four-cuntz-family`.

**Claim.** Let `sigma` be a char-`p` rank model of `R^x`, read as a model of `EL_4(R)`. If
`D = N_23 N_12 != 0`, there are an idempotent `e` of positive rank and `S_0, S_1, T_0, T_1` in
`eMe` with `T_i S_j = delta_ij e` and `S_0 T_0 + S_1 T_1 = e`.

**Why it closes the gate.** A corner family like that is excluded (L1). So `D = 0`, and
`el3-unit-root-matrix-units-iff-two-root-identities` together with
`matrix-unit-rank-models-extract-ring-rank-models` gives triviality.

**Why the verified obstructions miss it.**
* It is operator-level, not rank values. *(lead)* That holds only if the construction uses the
  regularity or rank of `M` at an intermediate step (L4a).
* It uses the Leavitt relations, the input `fd-represented-coefficients-violate-two-root-identities`
  demands.
* Property (T) and rounding are not invoked.

**First lemma.** On two root pairs of `EL_4(R)` the isometry commutators hold:
`[x_12(t_i), x_23(s_j)] = x_13(delta_ij)` and `[x_23(t_i), x_34(s_j)] = x_24(delta_ij)`. The cross
frame ties the two pairs through the shared index 3.

*(lead)* The first landing said that the telescoping "is now a Steinberg identity". That was never
shown, and by L4a it cannot be an identity of the group algebra. `S_j`, `T_i` and `e` are still
undefined (L3).

## Plan 2: the Heisenberg centre pairing

Node `heisenberg-centre-pairing-constrains-two-root-defect`. The unipotent radical of `EL_3` is
two-step nilpotent with centre `x_13(R)`. The commutator pairing `beta(a,b) = n_13(ab)` takes values
in a bounded-rank abelian square-zero group and is onto `R`, since `1 = s_0 t_0 + s_1 t_1`. The plan
is to turn this tension into an infinite orthogonal chain unless `D = 0`. That is not yet a
contradiction: the cross term of the branch split is uncontrolled.

## Plan 3: the algebra dichotomy

Node `leavitt-unit-linear-soficity-is-ring-rank-approximability`. It claims that `R^x` is
`F_p`-linear sofic if and only if `R` has unital maps `phi : R -> M_n(F_p)` that are multiplicative
up to rank `eps` on finite sets and respect the Leavitt relations up to rank `eps`.

*(lead) Correction.* The right-hand property is **false** for `R`. The ultraproduct of such maps
would be an exact unital ring homomorphism `R -> M`, which `leavitt-algebra-has-no-unital-rank-model`
excludes. So the equivalence only says "`R^x` is not `F_p`-linear sofic", which is the target
itself, and its backward direction is vacuous.

"Approximately proper isometries" cannot persist either. In `M_n(k)`, suppose `TS = 1 - E` with
`rk E < eps n`.
* Then `rk S`, `rk T >= (1 - eps) n`, so `F = ST` has `rk F >= (1 - 2 eps) n`.
* `F^2 - F = -SET` has rank `< eps n`.
* So `1 - F` has rank `< eps n` on `im F`, which has codimension `<= 2 eps n`, and
  `rk(1 - ST) < 3 eps n`.

The node restates the target rather than reframing it. It should be restated or retired.

## Ranking

1. Plan 1, as the family target, with L1--L4 as its interface.
2. Plan 3, demoted *(lead)* to a restatement of the target.
3. Plan 2, independent but not yet a contradiction.

## L. Lead integration (family R4)

### L1. Minimal target: one proper isometry; completeness is not used

Let `e != 0` be an idempotent and `S_0, S_1, T_0, T_1` elements of `eMe` with

```text
T_0 S_0 = e,     T_1 S_1 = e,     T_1 S_0 = 0 .
```

Then `(T_0 + 1 - e)(S_0 + 1 - e) = 1`. A rank ultraproduct is directly finite, so
`(S_0 + 1 - e)(T_0 + 1 - e) = 1`, which is `S_0 T_0 = e`. Hence `T_1 = T_1 S_0 T_0 = 0` and
`e = T_1 S_1 = 0`, a contradiction. The relation `T_0 S_1 = 0` and completeness
`S_0 T_0 + S_1 T_1 = e` are not used. So **check (ii) is not needed** for the route, and the family
target is (i) for three relations plus (iii).

### L2. Logical status

A corner family as in L1 is impossible. Given the established nodes, "`D != 0` implies such a family"
is therefore equivalent to "`D = 0` always", which is the gate. The plan node carries no content
beyond a construction, and (iii), `e != 0` whenever `D != 0`, carries all of the weight.

### L3. The baseline candidate, and why it is circular

In `F_2[R^x]` put `tau(a) = (x_12(a) - 1)(x_21(1) - 1)`. Let `pi : F_2[R^x] -> M_3(R)` be the linear
extension of `R^x = GL_3(R)`, so `pi(tau(a)) = a E_11`. Extend `sigma` linearly to `F_2[R^x]`.

The candidate `T_i = sigma(tau(t_i))`, `S_j = sigma(tau(s_j))`, `e = sigma(tau(1)) = N_12 N_21` is the
matrix-unit extraction. Each relation of L1 is `sigma` applied to a nonzero element of `ker pi`, for
example `tau(t_1) tau(s_0)`. The regular representation does not kill such an element, so group
relations never force `sigma` to kill it. Forcing it is the gate itself. Theorem 3 of
`el3-two-root-self-similarity-2026-09-12.md` shows that the forcing fails over rank-modelled
coefficients.

A four-index candidate must replace `tau`, and the first landing did not supply one. **Open task
(w4-r4-orth): fix one definition of `S_j`, `T_i` and `e`, and land it here before checking (i)**, so
that (i) and (iii) are checked on the same objects.

### L4. Two calibrations every construction must pass

**(a) Kaplansky calibration.** Suppose the relations of L1 held, with `e != 0`, for elements of the
group algebra `F_2[R^x]` itself.
* The argument of L1 shows that `F_2[R^x]` is not directly finite.
* That refutes Kaplansky's direct finiteness conjecture for `R^x` in characteristic two.
* By Elek--Szabo (sofic groups satisfy the conjecture), it makes `R^x` **non-sofic**, which is far
  stronger than the gate.

Such constructions are not expected. **Check (i) must use the von Neumann regularity or the rank
function of `M` at an intermediate step**, for instance range idempotents `q` with `PM = qM`, as in
`leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`. Group relations, the Leavitt
relations and direct finiteness alone do not suffice.

**(b) Test bed for (iii).** Theorem 3 of the self-similarity artifact gives, for any coefficient
ring with a unital rank model (for instance `F_2`), models with `rk(N_23 N_12) = 2/9`. If a proof of
(iii) uses only Steinberg relations and rank, it applies there, and the chosen `e` must have
positive rank in those models. Computing `e` in the 2/9 models is a paper check for w4-r4-corner and
w4-r4-adversary. If `e = 0` there, the proof of (iii) must use the Leavitt relations as well.

### L5. Folding w4-gate-descent

Lane w4-gate-descent works on the nested defect pieces `q_k` of w3-gate-bridge-b (b62a0dc006), with
`delta_k = rk(q_k)`. Its goal is a uniform bound `delta_(k+1) >= c delta_k`. Together with
`R ~= R^2` this gives approximately multiplicative unital maps `phi_k : R -> q_k M q_k`. The finish:
* Renormalize the rank of `q_k M q_k` by `1/delta_k`.
* Suppose that on each finite `F` in `R` the multiplicativity errors are `o(delta_k)` in absolute
  rank.
* Then the ultraproduct over `k` of the renormalized corners is a rank ultraproduct, and
  `(phi_k)_omega` is an exact unital ring homomorphism into it, contradicting
  `leavitt-algebra-has-no-unital-rank-model`.

**Caveat.** Absolute errors that are only `o(1)` do not suffice, because `delta_k` can decay
geometrically. The relative bound is the check. The route uses rank, so L4a does not bite. The
Toeplitz group calibration (6ebb4155b8) is its test bed.

### L6. Status at this pass

| item | lane | status |
|---|---|---|
| (i) three relations of L1 | w4-r4-orth | open; definition of `S_j`, `T_i`, `e` first (L3); L4a applies |
| (ii) completeness | w4-r4-complete | not needed for the route (L1) |
| (iii) `e != 0` from `D != 0` | w4-r4-corner | open; carries the whole gate (L2); test bed L4b |
| break the plan | w4-r4-adversary | L4a, L4b |
| approximability node | w4-r4-approx | collapses to the target (Plan 3 correction) |
| Heisenberg node | w4-heisenberg | open |
| relative descent bound | w4-gate-descent | open; relative-error caveat (L5) |
| verification | w4-vf-gate | none landed at this pass |
