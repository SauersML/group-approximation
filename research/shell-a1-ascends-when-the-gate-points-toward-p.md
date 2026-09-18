---
rg: 2
id: shell-a1-ascends-when-the-gate-points-toward-p
kind: claim
title: If the shell germ gate ascends toward the singular point, the one-singularity stabilizer is an ascending HNN extension of a finitely generated shift-free subgroup
distinct_from:
  shell-fp-stabilizer-forces-fp-germ-group: that proves A_1 f.p. implies Q f.p. and leaves the converse open because K is not finitely generated; this proves a partial converse, reducing A_1 to a finitely generated subgroup D with no shift, when the gate points toward p.
  shell-germ-fp-is-an-ascending-hnn-gate: that characterizes finite presentation of the germ group Q; this lifts the same ascending structure from Q to the stabilizer A_1, where the non-finitely-generated kernel K lives.
  v-point-stabilizers-are-ascending-hnn-extensions-of-v: that is the case Q = <tau>, where D is a copy of V; this handles every germ group whose gate points toward p.
requires:
  - v-point-stabilizers-are-ascending-hnn-extensions-of-v
  - shell-fp-stabilizer-forces-fp-germ-group
artifacts:
  - research/artifacts/gq-bh-bh-free-07-classical-ledger.md
---

**ESTABLISHED** by `shell-a1-ascends-when-the-gate-points-toward-p-proof`
(lane proof, elementary; not independently reviewed; no priority claimed).

## Setting

- The shell envelope is `E = E_nu` for an infinite finitely generated input `P`, with
  singular point `p = 0^infinity`.
- `A_1 = {e in E : sing(e) ⊆ {p}, e(p) = p}`, and `Q = (E)_p` is its germ group.
- `K = ker(A_1 -> Q) = union_n K_n`, with `K_n` as in
  `v-point-stabilizers-are-ascending-hnn-extensions-of-v`. The kernel is `K` by
  `shell-fp-stabilizer-forces-fp-germ-group`.
- `t` in `V` is the element of that node, and `tau` in `Q` is its germ. `tau` moves cells
  toward `p`.
- `eta : Q -> Z` is the homomorphism with `eta(tau) = 1` and `ker(eta) = Q^0`, where `Q^0` is
  the near-index-zero germs. `A_1^0` is the preimage of `Q^0` in `A_1`.

**Hypothesis (G+), the gate pointing toward p.** There is a finitely generated
`B <= Q^0` with

    B <= tau B tau^-1   and   Q^0 = union_(n >= 0) tau^n B tau^-n.

## Statement

Assume (G+). Let `b_1, ..., b_r` generate `B` and choose any lifts `b^_i` in `A_1^0`.
There is `M >= 2` such that `D = <K_M, b^_1, ..., b^_r>` satisfies:
1. `t^-1 D t <= D` and `union_(n >= 0) t^n D t^-n = A_1^0`;
2. `A_1 = A_1^0 ⋊ <t>` is isomorphic to the ascending HNN extension `D *_phi`, where
   `phi(d) = t^-1 d t`.

Consequently:
- `A_1` is finitely presented whenever the finitely generated group `D` is.
- More generally, `A_1` has type `F_n` whenever `D` does.
- `D` has no shift: its image in `Q` is `B <= Q^0`.

## What this changes

`shell-fp-stabilizer-forces-fp-germ-group` leaves open whether `Q` f.p. implies `A_1` f.p.,
because `K` is not finitely generated. Under (G+) the non-finitely-generated part is
absorbed exactly as for `Stab_V(p)`: `t` stretches `K_M` onto `K_(M+1)`. The open part
becomes finite presentation of one explicit finitely generated group `D`, which contains a
copy `K_M` of `V` and whose germs all have near index 0.

## Scope and limits

- **The reverse direction (G−),** `B <= tau^-1 B tau` with `Q^0 = union tau^-n B tau^n`:
  the construction fails, because `K` ascends under `t` while `Q^0` ascends under `t^-1`.
  Whether `A_1` can be finitely presented in that case is not addressed.
- **Which gate is on main.** `shell-ascending-gate-is-a-finite-window-inclusion` states its
  gate for `R_nu` with a sign `eps`. How that sign corresponds to (G+) or (G−) at the level
  of `Q` is the fiber-product bookkeeping of `shell-germ-group-has-index-two-fiber-product`.
  (G+) should correspond to `eps` pointing toward `p` (lane expectation, not checked here).
- **What is not claimed.** Nothing here says `D` is finitely presented. For shell inputs,
  the `b^_i` move cells regularly, so `D ∩ K` can be larger than `K_M`, possibly all of `K`.
- **What remains.** Finite presentation of `D` is a shift-free lift problem. Whether it holds
  for some input that is not virtually cyclic is OPEN.
