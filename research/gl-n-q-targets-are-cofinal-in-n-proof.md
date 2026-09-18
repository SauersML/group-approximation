---
rg: 2
id: gl-n-q-targets-are-cofinal-in-n-proof
kind: route
title: Block embeddings and the adjoint representation
target: gl-n-q-targets-are-cofinal-in-n
requires: []
---

**The maps.** Each map is a homomorphism because block multiplication, the
determinant and conjugation are multiplicative.
- **`diag(g, 1)`.** Injective: `diag(g,1) = I` forces `g = I`.
- **`diag(g, det(g)^-1)`.** Has determinant `1`, and is injective for the same
  reason.
- **`[diag(g,1)]` in `PGL_(n+1)(Q)`.** If `diag(g,1)` is the scalar `λI`, the
  last diagonal entry gives `λ = 1`, so `g = I`.
- **Adjoint map.** `g X g^-1 = X` for all `X ∈ M_n(Q)` makes `g` central in
  `M_n(Q)`, hence scalar. So the kernel of `GL_n(Q) -> GL(M_n(Q))` is exactly
  the centre, and `PGL_n(Q)` embeds in `GL(M_n(Q)) ≅ GL_(n^2)(Q)`.

**Equivalences.** `P` is inherited by subgroups.
- (1 ⇒ 2) is trivial.
- (2 ⇒ 1): given `m >= 2`, pick `n >= m` with `P(GL_n(Q))`. Iterating the first
  map gives `GL_m(Q) <= GL_n(Q)`.
- (1 ⇒ 3): `SL_n(Q) <= GL_n(Q)`.
- (3 ⇒ 2): `GL_(n-1)(Q) <= SL_n(Q)` for each of the infinitely many `n`.
- (1 ⇒ 4): `PGL_n(Q) <= GL_(n^2)(Q)`.
- (4 ⇒ 2): `GL_(n-1)(Q) <= PGL_n(Q)` for each of the infinitely many `n`.

The monotonicity statement is the first map. The last paragraph of the target
is the cited closure node.
