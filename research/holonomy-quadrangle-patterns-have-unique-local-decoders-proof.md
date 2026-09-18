---
rg: 2
id: holonomy-quadrangle-patterns-have-unique-local-decoders-proof
kind: route
title: Build a global Π-potential on value positions from (H), make value relations global by (Q), push the decoder into F_q[Π] as a unit, then the reader columns of two gadgets collide against (R)
target: holonomy-quadrangle-patterns-have-unique-local-decoders
requires: []
artifacts:
  - research/artifacts/holonomy-quadrangle-local-decoder-uniqueness-2026-09-17.md
---

This is a direct proof in §§2-5 of the artifact.

- **Lemma 1 (split classes).** Uses (L) and (R).
  - For `c ~ c'`, the class `R(c, c')` is the graph of a pointer permutation `π_{c,c'}` plus a
    value-only part `ν_{c,c'}`.
  - There are no mixed U/V pairs.
  - The `π` compose, and `π = 1` iff `c = c'`.
- **Lemma 2 (global potential).** Uses (H).
  - Γ has the value edges `ν`, labelled by `π`.
  - A closed walk is a class word fixing a value position, so by (H) its pointer label is `1`.
  - Hence every component `C` carries an injective potential `φ: C -> Π`.
- **Lemma 3.** Uses (Q). If `π_{c,c'} = π_{d,d'}`, then `ν_{c,c'} = ν_{d,d'}`.
- **Lemma 4.** `γ_c = π_{c_ρ, c}` is injective on `ρ`, and the site coordinate `κ_ρ` is well defined.
- **Proposition 5.** Pushing (D) forward gives:
  - `s_ρ T_{C(o)} = δ_{κ(o)}` in `F_q[Π]`, and `0` on the other components;
  - `Π` finite, so `s_ρ` is a unit and the decoder is unique.
- **Theorem A.** Take two gadgets and put `τ = T_{C(o)}`.
  - The weights `τ^{-1}(x) τ(x^{-1})` and the reader columns `e_x = φ^{-1}(x^{-1})` do not depend on
    the gadget.
  - The "same site" partition is given by Lemma 3, and so is the same for both gadgets.
  - The unique class with nonzero total weight gives `X_ρ = X_{ρ'}`.
  - So `c_x e_x = o = d_x e_x` with `c_x != d_x`, which contradicts (R).
- **Corollary B.** Slice independence plus Theorem A.1 give `Σ_i r_i <= 1`, and hence `Phi >= log q`.
