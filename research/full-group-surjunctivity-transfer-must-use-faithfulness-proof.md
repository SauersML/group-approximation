---
rg: 2
id: full-group-surjunctivity-transfer-must-use-faithfulness-proof
kind: route
title: Realize any group as the image of a free group acting minimally, and turn factor-compatible cocycles into Lipschitz sections of the quotient map
target: full-group-surjunctivity-transfer-must-use-faithfulness
requires: []
artifacts: []
---

**Paradigm rule.**
- *Why this works where earlier routes failed.* It is an obstruction. It explains why full-group hosts built from
  surjunctive acting groups have not delivered a transfer: the hypothesis on the acting group is empty once
  faithfulness is dropped.
- *First falsifiable step.* In Theorem B, freeness of `Q ↷ X_Q` forces `p(c) = q` for every local cocycle value `c` of
  `ψ_q`.
- *Calibration.* `G = Z`, where Juschenko--Monod gives amenable full groups.

## Theorem A

`(⇐)`. Gottschalk says every group is surjunctive, which gives `T(C)` for every `C`.

`(⇒)`. Assume `T({F_2})`.

1. **Reduce to 2-generated groups.** Surjunctivity is local and passes to subgroups (Ceccherini-Silberstein--Coornaert).
   Every countable group embeds in a 2-generated group (Higman--Neumann--Neumann). So it suffices to show that every
   countably infinite 2-generated group `Q` is surjunctive. Finite groups are sofic.
2. **The host.** Let `Q = <s_1, s_2>` be countably infinite. By Gao--Jackson--Seward, `Q` has a free minimal subshift
   `X_Q`. An infinite minimal system has no isolated points, so `X_Q` is a Cantor space.
3. **The action.** Let `p: F_2 -> Q` send `a_i` to `s_i`, and let `F_2` act on `X_Q` through `p`. The orbits are the
   `Q`-orbits, so the action is minimal.
4. **The embedding.** Every element `q` in `Q` is `p(g)` for some `g` in `F_2`. So the homeomorphism
   `x -> q x` equals `g` everywhere, which puts it in `[[F_2 ↷ X_Q]]`. The map `q -> (x -> q x)` is a homomorphism.
   It is injective because the `Q`-action is free.
5. **Conclude.** So `Q <= [[F_2 ↷ X_Q]]`, and `T({F_2})` makes `Q` surjunctive.

If `C` contains `F_2`, then `T(C)` implies `T({F_2})`. So `T(C)` is also equivalent to Gottschalk.

The only property of `F_2` used is that it maps onto every 2-generated group. So the step that fails for any
transfer is the passage from `G` to its image in `Homeo(X)`.

## Theorem B

Setting: `p: F_r -> Q` is onto, `Q ↷ X_Q` is free, `F_r ↷ Y` is free, `X = X_Q × Y`, and `g(x, y) = (p(g)x, gy)`.

- **Faithful and free.** `F_r` acts freely on `X`, since it acts freely on `Y`. In particular the action is faithful.
- **Cocycles.** Let `ψ: Q -> [[F_r ↷ X]]` be an injective homomorphism with `π ∘ ψ_q = q ∘ π`, and let
  `S = {s_1, ..., s_k}` generate `Q`.
  - For `z` in `X`, there is a unique `c_i(z)` in `F_r` with `ψ_{s_i}(z) = c_i(z) z`. It exists by the definition of
    the full group, and it is unique by freeness.
  - `c_i` is locally constant on a compact space, so it takes finitely many values. Let `M` be the largest word
    length among them.
- **The section `L`.** Fix `z_0` in `X` with `x_0 = π(z_0)`. For `q` in `Q`, let `L(q)` be the unique element of
  `F_r` with `ψ_q(z_0) = L(q) z_0`.
  - *Section.* Compare first coordinates: `q x_0 = π(ψ_q z_0) = p(L(q)) x_0`. The `Q`-action is free, so
    `p(L(q)) = q`.
  - *Lipschitz.* `ψ_{s_i q}(z_0) = ψ_{s_i}(L(q) z_0) = c_i(L(q) z_0) L(q) z_0`. By freeness,
    `L(s_i q) = c_i(ψ_q z_0) L(q)`.
  - *Metrics.* Use right-invariant word metrics `d(g, h) = |g h^{-1}|`. Then
    `d_F(L(s_i q), L(q)) = |c_i(ψ_q z_0)| <= M`, while `d_Q(s_i q, q) = 1`. So `L` is `M`-Lipschitz, and `p` is
    1-Lipschitz.
- **Quasi-isometric embedding.** For all `q, q'` in `Q`:
  `d_Q(q, q') = d_Q(p L q, p L q') <= d_F(L q, L q') <= M d_Q(q, q')`.
  So `L` is a quasi-isometric embedding of `Q` into the Cayley tree `T` of `F_r`.
- **Virtually free.**
  - Asymptotic dimension does not increase under coarse embeddings, so `asdim Q <= asdim T = 1`.
  - A finitely generated group with `asdim <= 1` is virtually free (Gentimis; also Fujiwara--Whyte), or finite when
    the dimension is 0.
  - Virtually free groups are residually finite, so they are sofic, and by Gromov--Weiss they are surjunctive.

Calibration: replacing `F_r` with `Z` gives `asdim Q <= 1` with polynomial growth of degree 1, so `Q` is virtually `Z`.
This matches amenability of `[[Z ↷ X]]`.

The lower bound `d_Q <= d_F ∘ L` uses only that `p` is a Lipschitz left inverse. That is exactly the failing step:
the free factor on which `Q` acts pins each cocycle value to a lift of `q`.
