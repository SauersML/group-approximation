---
rg: 2
id: baumslag-gersten-odometer-pieces-force-fixed-points
kind: claim
title: If a acts as a minimal equicontinuous rotation on a compact piece invariant under a and b, then b fixes a point there and a has a fixed point, so odometer models of BS(1,2) never extend to the Baumslag--Gersten group
distinct_from:
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that constrains actions of the Baumslag--Gersten group on trees through translation lengths; this constrains its actions on compact spaces through the dynamics of a on an invariant piece.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that transfixes commensurated sets for groups with property FW; this applies to the Baumslag--Gersten group, which has no FW, and excludes odometer images of a instead.
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed).

Let `BG = < a, t | b a b^-1 = a^2 >`, with `b = t a t^-1`, act by
homeomorphisms on a Hausdorff space `X`. Let `Y ⊆ X` be a compact metrizable
subset with at least two points, invariant under `a` and `b`, on which `a` is
minimal and equicontinuous.

1. **Fixed points.** `b` has a fixed point `y ∈ Y`, and `a` fixes `t^-1 y`.
2. **No odometer action.** No action of `BG` on a compact metrizable space with
   at least two points has `a` minimal and equicontinuous.
3. **The standard models do not extend.**
   - **Affine ternary model.** The self-similar affine model of `BS(1,2)` on
     `Z_3` has `a: x ↦ x + 1` and `b: x ↦ 2x`. It extends to no `BG`-action on
     `Z_3`.
   - **Adding machine.** More generally, no embedding of `BG` into a group of
     homeomorphisms of `Y` sends `a` to an adding machine on `Y`. This includes
     Röver--Nekrashevych groups `V_d(H)` built on such a model.
   - **Projective 2-adic model.** In the model on `P^1(Q_2)` with `a: x ↦ x + 1`
     and `b: x ↦ 2x`, `a` fixes only `∞` while `b` fixes `0` and `∞`. Since `b`
     is conjugate to `a` in `BG`, the model extends to no `BG`-action.

The fixed-point step uses `1 - 2 = -1`, so the statement is for `BG = BG_2` only.
The proof is `baumslag-gersten-odometer-fixed-point-proof`.
