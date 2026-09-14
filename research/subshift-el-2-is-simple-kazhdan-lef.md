---
rg: 2
id: subshift-el-2-is-simple-kazhdan-lef
kind: claim
title: For every infinite minimal subshift X, EL_2(LC(X,F_2)⋊Z) is an infinite finitely generated simple Kazhdan LEF group; EL_2(LC(X,F_q)⋊Z) is Kazhdan for every q
distinct_from:
  cyclic-factor-subshift-el-2-is-simple-kazhdan-lef: that covers only X with a finite cyclic factor, by a Morita reduction; this covers every infinite minimal X, e.g. Sturmian ones, through complementary full idempotents.
  steinberg-elementary-groups-are-simple-mod-centre: that is simplicity of EL_n/Z with n ≥ 3 over Steinberg algebras; this is rank two over subshift algebras with F_2 coefficients.
---

**ESTABLISHED (unreviewed)** by `subshift-elementary-el-2-simple-kazhdan-lef-proof`.

**Statement.** Let `X` be an infinite minimal subshift, `q` a prime power, and `R = LC(X,F_q) ⋊_T Z`.
1. `EL_2(R)` is infinite, finitely generated, and has property (T).
2. For `q = 2`, `EL_2(R)` is simple with trivial centre, and LEF, hence sofic and hyperlinear.

So the note's theorem (main tip, l.53: "for every $n\ge3$") holds for every `n ≥ 2`. This answers
`el-2-over-every-minimal-subshift-algebra-is-kazhdan`.

**Scope.** Simplicity modulo the centre for `q > 2` is NOT claimed. The binary unit trick `LC(X,F_2)^× = {1}` fails over `F_q`.

**Review (sk-verify-4, 2026-09-13): PASS.** Fullness of `e_W` and `e_(X∖W)`, (T), LEF, and simplicity over `F_2` (binary scalar step, the tower copy `GL_d(F_2)` with `d = 2(2w+1)`, and the six-step level propagation through three Peirce blocks) re-derived. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §5.
