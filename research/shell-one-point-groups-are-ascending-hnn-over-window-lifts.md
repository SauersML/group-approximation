---
rg: 2
id: shell-one-point-groups-are-ascending-hnn-over-window-lifts
kind: claim
title: If the shell germ group has an ascending window in the direction of the V-germ, the one-point group A_1 is an ascending HNN extension of an explicit lift of that window, so A_1 has every finiteness property the lift has
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - bhm-singfix-condition-forces-fp-germ-groups
distinct_from:
  shell-germ-fp-is-an-ascending-hnn-gate: that characterizes finite presentation of the germ group Q and records that sufficiency for A_1 is open; this proves a sufficient condition for A_1 itself, in one of the two directions of the gate.
  bhm-singfix-condition-forces-fp-germ-groups: that goes down from A_1 to its germ group; this goes up from a window of the germ group to A_1.
---

**ESTABLISHED** (lane proof, bh-free-08, 2026-09-18; elementary; not reviewed; no novelty claimed).

## Setting

- **The shell.** `E_ν` is the shell envelope of a countably infinite `P` with enumeration `ν`, from `shell-cantor-embeddings-are-finite-germ-extensions`. Here `p = 0^∞` and `C_m = [0^m]`.
- **The one-point group.** `A_1 = SingFix_(E_ν)({p},{p})`, with the germ map `π: A_1 → Q = (E_ν)_p`. `π` is onto with kernel `K = RStab_V(p) = ⋃_m V_m`, where `V_m` is the group of elements of `V` supported in `C ∖ C_m` (`bhm-singfix-condition-forces-fp-germ-groups`).
- **The shift and its lift.** `τ ∈ Q` is the germ of `V` at `p`, sending block `[0^n1]` to block `[0^(n+1)1]`, and `η: Q → Z` is the near index, with `η(τ) = 1`. Put `Q^0 = ker η`. Let `t ∈ V` be `0x ↦ 00x`, `10x ↦ 01x`, `11x ↦ 1x`. Then `t` fixes `p`, has germ `τ`, satisfies `t(C_m) = C_(m+1)`, and so `t V_m t^{-1} = V_(m+1)` for `m ≥ 1`.

## Statement

Suppose **(W+)**: there is a finitely generated `B ≤ Q^0` with `τ^{-1} B τ ⊆ B` and
`Q^0 = ⋃_(n≥0) τ^n B τ^{-n}`. Fix generators `b_1, …, b_r` of `B` and lifts `b̃_i ∈ A_1` with `π(b̃_i) = b_i`. Then:

1. For some `m ≥ 2`, the group `B̃ = ⟨V_m, b̃_1, …, b̃_r⟩` satisfies `t^{-1} B̃ t ⊆ B̃`. Moreover `A_1` is the ascending HNN extension `B̃ *_φ`, with `φ(x) = t^{-1} x t` and stable letter `t`.
2. Consequently, if `B̃` has type `F_n` (respectively `FP_n`), so does `A_1`. By `bhm-singfix-condition-forces-fp-germ-groups`, so do `Q` and its index-two fiber product.

(W+) is one of the two directions allowed in `shell-germ-fp-is-an-ascending-hnn-gate`: `ε = +1` in the convention where `V`'s own union `K = ⋃ t^n V_m t^{-n}` increases. The direction `ε = −1` is not covered, since there `V_m` and `B` ascend under opposite powers of `t`.

## Proof

**The corrections.** `τ^{-1} b_i τ ∈ B`, so `τ^{-1} b_i τ = w_i(b)` for a word `w_i`. In `A_1` the elements `t^{-1} b̃_i t` and `w_i(b̃)` have the same germ, so `t^{-1} b̃_i t = w_i(b̃) k_i` with `k_i ∈ K`. Choose `m ≥ 2` with every `k_i ∈ V_m`.

**The inclusion.**
- `t^{-1} V_m t = V_(m-1) ⊆ V_m`.
- `t^{-1} b̃_i t = w_i(b̃) k_i ∈ B̃`.

So `t^{-1} B̃ t ⊆ B̃`, and the conjugates `t^n B̃ t^{-n}` increase with `n`.

**The union.** Let `A_1^0 = ker(η∘π)`.
- `B̃ ≤ A_1^0`: `V_m ≤ K`, and `π(b̃_i) ∈ Q^0`.
- `t` normalizes `A_1^0`.
- `U := ⋃_n t^n B̃ t^{-n}` contains `⋃_n V_(m+n) = K`.
- `π(U)` contains `⋃_n τ^n B τ^{-n} = Q^0`.

So `U = π^{-1}(Q^0) = A_1^0`. Since `η(π(t)) = 1`, `A_1 = A_1^0 ⋊ ⟨t⟩`, with `A_1^0` the increasing union of the `t`-conjugates of `B̃`. That is the ascending HNN extension `B̃ *_φ`.

**Finiteness.** An ascending HNN extension of a group of type `F_n` has type `F_n`: apply Brown's criterion to the Bass–Serre tree, as in BHM arXiv:2407.03149v1, TeX line 1304. The same argument works for `FP_n`. ∎

## Remarks (not claimed)

- **When `B̃` contains all of `K`.** `B̃ ∩ K ⊇ V_m` together with its conjugates under `⟨b̃_i⟩`. When the germs in `B` carry the blocks of `C ∖ C_m` over all of `C ∖ {p}`, and the translates overlap in a connected pattern, `B̃ ∩ K = K`. This happens for shells: `ρ(P)` is transitive on the even blocks, and the `τ`-conjugates reach the odd ones. Then `B̃` is an extension of the finitely generated window `B` by the non-finitely-generated group `K`. It is a "V-lampshuffler", the disjoint-union analogue of a twisted Brin–Thompson group.
- **Why this does not beat the type (A) route.** By analogy with FFWZ, finiteness of such a `B̃` is expected to need `B`'s block action to have finitely many orbits of pairs and finitely generated block stabilizers. That is a type (A) or `[HA_2]`-type action of a group containing `P`. Such an action would give an envelope directly through the twisted Brin–Thompson group. So this sufficient condition is not expected to be easier than `every-countable-group-lies-in-a-faithful-ha2-actor` or the permutational conjecture. Showing `A_1` finite needs a base other than `B̃`, or an argument that uses `t` itself.
