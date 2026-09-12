---
rg: 2
id: leavitt-kernel-corner-embedding-proof
kind: route
title: Cut the scalar copy of the group algebra by the constant C_3 averaging idempotent
target: leavitt-unit-group-algebra-embeds-in-kernel-corner
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Sections 1–3 of the artifact.

1. `delta(q) = Theta_2(q I_2)` is an injective homomorphism. It commutes with every
   constant `Theta_2(C)`, `C` in `GL_2(F_2)`, and meets that copy only in `1`, since
   `q I_2 = C` forces `q = 1`.
2. `z = [1] + [g] + [g^2]` is idempotent in characteristic two. It evaluates to
   `Theta_2(I + g + g^2) = 0`, because the natural representation of the 3-cycle has
   no fixed vector.
3. `delta(x) z delta(y) z = delta(xy) z`, and `delta(x) z = 0` forces `x = 0` in
   `F_2[delta(G)] (x) F_2[H]`. So `j` is an injective unital ring map into `zSz`,
   which lies in `K`.
4. Padding by `e = 1 - z` gives `Phi`, with `Phi(x) - 1 = (delta(x) - 1) z` in `K`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 13 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
