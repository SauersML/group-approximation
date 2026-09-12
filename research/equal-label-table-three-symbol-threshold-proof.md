---
rg: 2
id: equal-label-table-three-symbol-threshold-proof
kind: route
title: A block involution unmasks relay one over three symbols, and over two symbols the column bijections cannot differ
target: equal-label-table-is-strict-at-three-symbols-not-two
requires: []
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Theorem 6.2, rows `B ~ A`, of the artifact.
- **The decoder identity.** It reads `nu(mu(c,w), mu(w,v)) = c`.
- **Three or more symbols.**
  - Relay `a` outputs a symbol in the block of the shared cell `w`, relay `1` outputs
    `g_B(w)(c)`, and the sink undoes the involution.
  - In reverse, relay `b`'s output lies in the block of `q(b,1)`, so the sink returns
    `g_B(q(b,1))(g_B(q(1,a))(q(1,1)))`.
  - When `q(1,a)` and `q(b,1)` can take symbols in different blocks, this is `(0 1)(0) = 1 != 0` for
    a suitable choice of `q(1,1)`.
- **Two symbols.**
  - Each column map `h_w = mu(.,w)` is a bijection, and `nu(.,z) = h_w^-1` on the relay-`a` image
    `J_w`.
  - Distinct `h_0, h_1` would make `J_0` and `J_1` disjoint singletons. Then `mu(u,v) = k(u)`,
    whence `h_0 = h_1`, a contradiction.
  - So `mu = h o pi_1`, the `J_w` cover `A`, and `nu = h^-1 o pi_1`.
