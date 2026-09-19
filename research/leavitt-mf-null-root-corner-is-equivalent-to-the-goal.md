---
rg: 2
id: leavitt-mf-null-root-corner-is-equivalent-to-the-goal
kind: claim
title: The Leavitt negative-root corner is MF-null iff the Leavitt Steinberg group has full MF radical, without Property (T)
distinct_from:
  leavitt-root-corner-algebra-is-mf-null: that is the hole (MF-nullity of P_z C[Delta] P_z) stated as if it were weaker than the goal; this proves, without (T), that the hole and property-t-free-leavitt-full-mf-radical imply each other, and records that the hole as literally stated is already true via (T).
  mf-null-corner-criterion-needs-faithful-ce-trace: that proves one direction for every group (MF-null torsion corner implies the root is in the MF radical) and kills tracial certificates; this proves a converse (the root in the MF radical of its own centralizer makes the corner MF-null) and applies it to the Leavitt root, where the centralizer contains a copy of the whole group.
  augmentation-lifting-equals-full-mf-radical: that is an earlier tool shown to be equivalent to the goal, a different one (augmentation lifting); this is the negative-root corner.
  leavitt-corner-host-is-the-simple-leavitt-unit-group: that identifies the corner host with the unit group; this uses a copy of St_18 inside the centralizer of the root to transport the radical into the corner.
  agent-leavitt-not-bcs-negative-root-corner: that asks for a no-CE BCS algebra mapped into the corner, which is strictly stronger (it forces nonhyperlinearity); this settles only the MF-nullity of the corner itself relative to the goal.
artifacts:
  - research/leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof.md
  - experiments/leavitt-corner-centralizer-2026-09-17/check_centralizer_chain.py
---

**ESTABLISHED** (route `leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof`, swarm-0917-w13-w13-ptl-pull,
2026-09-18, unreviewed). This is an obstruction to a class of approaches to `property-t-free-leavitt-full-mf-radical`.
It is not a proof of the goal, and the goal stays OPEN.

## Setting

- `Q_k` is the norm matrix corona, and "MF-null" is as in `mf-null-corner-criterion-needs-faithful-ce-trace`.
- For a countable group `G`, `Rad_MF(G)` is the intersection of the kernels of all homomorphisms `G -> U(Q_k)`, over all
  `k`. For countable groups this is the MF radical of `non_mf_groups_exist.tex`.
- For `z` in `G` of finite order `m`, put `q_z = 1 - (1/m) sum_(j<m) z^j`.
- `R = L_(F_2)(1,2)`, `Delta = St_20(R)`, `z = x_13(q)` with `q = s_1 t_1`, and `P_z = q_z = (1 - z)/2`.

## Statement

**(S) Centralizer sandwich, for any group.** Let `z` in `G` have finite order. Then

```text
z in Rad_MF(C_G(z))   ==>   q_z C[G] q_z is MF-null   ==>   z in Rad_MF(G).
```

The second implication is part (A) of `mf-null-corner-criterion-needs-faithful-ce-trace`. The first one is new.

**(R) Rank-two shift, for any ring.** Let `A` be a unital ring, `n >= 4`, and `a` in `A` such that `z = x_13(a)` has
finite order in `St_n(A)`. If `x_12(1)` lies in `Rad_MF(St_(n-2)(A))`, then `z` lies in `Rad_MF(C_(St_n(A))(z))`. So by
(S), the corner `q_z C[St_n(A)] q_z` is MF-null.

**(E) Leavitt equivalence, without Property (T).** The following are equivalent:

1. `Rad_MF(Delta) = Delta` (the goal `property-t-free-leavitt-full-mf-radical`);
2. `P_z C[Delta] P_z` is MF-null (the hole `leavitt-root-corner-algebra-is-mf-null`);
3. `z` lies in `Rad_MF(C_Delta(z))`.

The proof uses only the Steinberg relations, (S), (KH2) of `leavitt-steinberg-map-iso-from-rank-three`, the prefix-code
ring isomorphisms `M_n(R) = R`, and the normal generation `full-leavitt-idempotent-defect-saturation`. No step uses
Property `(T)`, stability, or any approximation input.

## The Property (T) corollary

`binary-leavitt-all-ranks-full-mf-radical` proves item 1 of (E) using Property `(T)`. So items 2 and 3 are **true**.

- The hole `leavitt-root-corner-algebra-is-mf-null`, as literally stated, is a theorem.
- Its only open content is the words "without (T)". Those words appear in its "Finite form" paragraph but not in its
  Statement.
- **Warning for the graph.** Suppose a route establishing that hole from `binary-leavitt-all-ranks-full-mf-radical`
  were linked. Then `leavitt-mf-null-root-corner-closes-full-radical` would mark the T-free goal ESTABLISHED
  dishonestly. The hole needs a T-free clause in its Statement, as `augmentation-lifting-equals-full-mf-radical` did.

## The class that dies

**The class.** Every route to `property-t-free-leavitt-full-mf-radical` that first proves the corner at a root element
`x_13(a)` of `Delta` is MF-null, and then applies criterion (A). This includes:

- `leavitt-mf-null-root-corner-closes-full-radical`;
- every operator-norm "finite form" certificate for `leavitt-root-corner-algebra-is-mf-null`.

**Why it dies.** A T-free proof of the corner statement is exactly as hard as a T-free proof of the goal. The corner
reformulation is an equivalent restatement, not a reduction.

**Invariant.** The centralizer of the root contains `M`, the copy of `St_18(R)` on the indices other than `1` and `3`.
By (KH2) and Morita, `M` is isomorphic to `Delta`. Two Steinberg commutators pass from `M` to `z` inside `C_Delta(z)`:

```text
x_1m(q) = [x_1l(q), x_lm(1)],    z = [x_1m(q), x_m3(1)]     (l, m distinct, not in {1,3}).
```

**Death step.** Restrict a unital corner representation `phi` to `C_Delta(z) P_z`. This gives a corona representation of
the centralizer with `rho(z) = -1`. That is the same object whose nonexistence the goal asserts, now for the copy `M`.

**What survives.**
- Corner statements that are strictly stronger than MF-nullity, such as `agent-leavitt-not-bcs-negative-root-corner`,
  which also forces nonhyperlinearity.
- Corners at projections whose stabilizer contains no rank-shifted copy of `Delta`.
- Direct attacks on the goal.

## Attempts

- **Converse of (S) (swarm-0917-w13-w13-ptl-pull, 2026-09-18). Open.** Does MF-nullity of `q_z C[G] q_z` imply
  `z in Rad_MF(C_G(z))` for every group?
  - A corona representation of `C_G(z)` with `rho(z) != 1` gives none of the corner. Induction from `C_G(z)` to `G`
    is not available in the norm corona.
  - For `Delta`, the converse holds by (E), but only because both sides are equivalent to the goal.
