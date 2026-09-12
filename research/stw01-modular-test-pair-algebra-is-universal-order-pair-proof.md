---
rg: 2
id: stw01-modular-test-pair-algebra-is-universal-order-pair-proof
kind: route
title: Dilate every Hilbert-space order pair into a corner of a representation of Q
target: stw01-modular-test-pair-algebra-is-universal-order-pair
requires: []
---

Full proof: Section 1 of `research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`.

1. **The pair satisfies (OP).** `h = e_1 p e_1` is a positive contraction, and
   `k = (e_2 p e_1)^*(e_2 p e_1)` satisfies `0 <= k <= k + e_1 p e_3 p e_1 = h - h^2`. So the
   unital *-homomorphism `phi : U -> Q` with `h_0 -> h`, `k_0 -> k` exists.
2. **Douglas factorization.** Let `a, b in B(H)` satisfy (OP). Put
   `S = (1 - a)^(1/2) a^(1/2)`, so `S^* S = a - a^2 >= b`. Douglas' lemma gives a contraction
   `C` with `b^(1/2) = C S`. With `d = (1 - a)^(1/2) C^* C (1 - a)^(1/2)` we get
   `0 <= d <= 1 - a` and `b = a^(1/2) d a^(1/2)`.
3. **Three-block projection.** The column `c = (a^(1/2), d^(1/2), (1 - a - d)^(1/2))^T`
   satisfies `c^* c = 1`, so `r = c c^*` is a projection in `M_3(B(H))`. Its entries are
   `r_11 = a` and `r_12 r_21 = a^(1/2) d a^(1/2) = b`. The unital *-homomorphism
   `rho : Q -> M_3(B(H))` with `e_j -> f_j` (diagonal matrix units) and `p -> r` gives
   `rho(h) = a (+) 0 (+) 0` and `rho(k) = b (+) 0 (+) 0`.
4. **Norms.** For every *-polynomial `P`,
   `rho(P(h, k)) = P(a, b) (+) P(0, 0) 1 (+) P(0, 0) 1`, so `||P(a, b)|| <= ||P(h, k)||_Q`.
   Taking the supremum over all Hilbert-space representations of (OP) gives
   `||P(h_0, k_0)||_U <= ||phi(P(h_0, k_0))||`. So `phi` is isometric on a dense
   *-subalgebra, hence injective.

**Trust boundary.** The inputs are:
- Douglas' lemma: `T^* T <= S^* S` in `B(H)` gives `T = C S` with `||C|| <= 1`;
- the universal properties of `U` and of the unital full free product `Q`;
- the fact that the norm of a universal C*-algebra is the supremum over Hilbert-space
  representations of its relations.
