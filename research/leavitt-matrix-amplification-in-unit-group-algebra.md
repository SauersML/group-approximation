---
rg: 2
id: leavitt-matrix-amplification-in-unit-group-algebra
kind: claim
title: Every two-power matrix algebra over the Leavitt unit group algebra embeds into a supported corner
distinct_from:
  leavitt-corner-idempotent-unital-surjection: that builds the corner `eAe` and its unital evaluation onto `R`, and is about a map out of the corner; this says what sits *inside* the same corner — a full matrix algebra over the whole group algebra — and it uses that node's idempotent as its starting point.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies `GL_n(R)` with `EL_n(R)` and is a statement about groups over the Leavitt algebra; this is a statement about matrix rings over the *group algebra* `F_2[R^x]`, one level up, and neither transports to the other.
  augmentation-blocks-unital-leavitt-family: that forbids a binary Leavitt family in any matrix ring over an integral group ring; this exhibits matrix rings over a group algebra inside that group algebra, and the two do not meet — the amplification carries no Leavitt relations.
  leavitt-unit-group-algebra-not-directly-finite: that is the open Kaplansky failure, an existence question about a one-sided inverse pair; this is an established embedding statement that supplies no pair and is neutral on the answer -- it only removes matrix size from the search.
  binary-leavitt-family-lifts-into-unit-corner: that asks for a full Leavitt family inside the same corner `eAe`, which would carry five multiplicative relations; this puts matrix algebras over the group algebra there instead, carries no Leavitt relation, and is established -- the two occupy the same corner and ask for unrelated things.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`.  For every `k >= 0` and
`N = 2^k` there is an injective ring homomorphism

    j_N : M_N(S) -> S

whose image is contained in `E_N S E_N` for the idempotent
`E_N = j_N(I_N)` of `S`, with `E_1 = 1` and
`E_2 = e = [g] + [g^2]`, the idempotent of
`leavitt-corner-idempotent-unital-surjection`.

In particular `e S e` contains a copy of `M_2(S)`.

No assertion is made that the image equals all of `E_N S E_N`.  The
construction proves an embedding supported by the corner, and that is exactly
what its direct/stable-finiteness consumer needs.

## Where the room comes from

Two commuting copies of structure inside the one group `G`, both visible only
through the self-similarity `Theta_2 : M_2(R) -> R`,
`Theta_2((a_ij)) = sum s_i a_ij t_j`:

* the **constant** matrices.  `H = <u, v> ~= GL_2(F_2) ~= S_3` is exactly
  `Theta_2(GL_2(F_2))` — the repository's own `u = 1 + s_0t_1`,
  `v = 1 + s_1t_0`, `w = u v u`, `g = uv` are `Theta_2` of
  `[[1,1],[0,1]]`, `[[1,0],[1,1]]`, `[[0,1],[1,0]]`, `[[0,1],[1,1]]`;
* the **scalar** matrices.  `delta(q) = Theta_2(q I_2) = s_0 q t_0 + s_1 q t_1`
  is `LeavittFamily.crossUnit`, an injective endomorphism of `G`.

Scalars commute with constants and meet them only in the identity, so
`delta(G) x H` embeds in `G` and `S (x) F_2[H]` embeds in `S`.  Cutting by `e`
and using `e F_2[H] e ~= M_2(F_2)` — a finite sixteen-element computation in a
six-element group algebra, certified exactly in
`research/artifacts/verify-s3-corner-2026-08-17.py` — gives `M_2(S)` inside
`e S e`.  Induction gives every two-power.

## What it is for, and what it is not

Its consumer is `leavitt-stable-finiteness-equals-direct-finiteness`, and
through that it removes matrix size from the search space of the whole
Kaplansky/Gottschalk lane.

It is **not** by itself any kind of infiniteness statement.  A ring can
contain proper corner copies of its own matrix algebras and still be directly
finite; directly finite non-Noetherian rings with proper corner
self-embeddings and infinitely many orthogonal idempotents exist.  Nothing
here decides `leavitt-unit-group-algebra-not-directly-finite` in either
direction — it only says the question does not get easier or harder with `n`.

It is also not a *unital* embedding: `E_N` has augmentation zero for `N >= 2`
(`eps(e) = 0`), and no unital copy of `M_2(S)` in `S` is claimed or possible
to obtain this way.
