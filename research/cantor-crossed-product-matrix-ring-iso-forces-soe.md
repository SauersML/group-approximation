---
rg: 2
id: cantor-crossed-product-matrix-ring-iso-forces-soe
kind: claim
title: If M_m(LC(X,k)⋊Z) and M_m(LC(Y,k')⋊Z) are isomorphic or anti-isomorphic rings, for minimal Cantor systems X and Y, then X and Y are strongly orbit equivalent
distinct_from:
  subshift-gl3-iso-gives-matrix-ring-iso-odd-q: that turns a GL_3 group isomorphism into a matrix ring (anti-)isomorphism for q odd; this turns a matrix ring (anti-)isomorphism into strong orbit equivalence, for every field and every m
  subshift-crossed-product-k0-is-coinvariant-group: that computes the abelian group K_0 without the order; this identifies the order cone and the unit and then applies Giordano–Putnam–Skau
artifacts:
  - research/artifacts/sk-rigidity-ring-2026-09-13-part1.md
  - research/artifacts/sk-rigidity-ring-2026-09-13-part2.md
---

Let `(X,T)` and `(Y,S)` be minimal homeomorphisms of Cantor sets, let `k, k'` be fields and let `m ≥ 1`. Put
`R_X = LC(X,k) ⋊_T Z` and `R_Y = LC(Y,k') ⋊_S Z` (algebraic crossed products). If `M_m(R_X) ≅ M_m(R_Y)` or
`M_m(R_X) ≅ M_m(R_Y)^op` as rings, then the unital ordered groups `(K^0(X,T), K^0(X,T)^+, [1])` and
`(K^0(Y,S), K^0(Y,S)^+, [1])` are isomorphic. So `(X,T)` and `(Y,S)` are strongly orbit equivalent.

Proof in the `-proof` route; details in artifact part 1 §1.
- Anti-isomorphisms reduce to isomorphisms through the anti-automorphism `Σ f_n u^n ↦ Σ u^(−n) f_n`.
- A ring isomorphism preserves `(K_0, K_0^+, m[1])`.
- `K_0(R_X) = C(X,Z)/(1−T_*)` (Theorem K).
- The idempotent cone equals the Herman–Putnam–Skau cone, via Ara–Claramunt's faithful measure rank functions and the
  positivity criterion for simple dimension groups.
- `K^0(X,T)` is torsion-free by minimality, so `m[1] ↦ m[1]` forces `[1] ↦ [1]`.
- Giordano–Putnam–Skau finish.

Scope:
- The conclusion is strong orbit equivalence, not flip conjugacy. Strong orbit equivalence classes contain systems of
  different entropy, so no argument through the unital ordered `K_0` alone gives more.
- The unit caveat recorded in `subshift-elementary-group-isomorphism-forces-orbit-equivalence` (height-3 towers) does
  not arise: torsion-freeness forces the isomorphism to send `[1]` to `[1]`.

**Review (sk-verify-3, 2026-09-13): PASS.** (R1)–(R6) re-derived: the anti-automorphism, the idempotent cone equal to the HPS cone through faithful Ara–Claramunt rank functions, the Bauer maximum principle and Effros's criterion, torsion-freeness, and GPS. Wiring note: `subshift-crossed-product-k0-is-coinvariant-group` is displayed for `F_q`, but its proof works over every field. See `research/artifacts/sk-review-3-2026-09-13-part4.md` §2.
