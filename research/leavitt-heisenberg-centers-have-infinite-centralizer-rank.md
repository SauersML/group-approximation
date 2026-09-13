---
rg: 2
id: leavitt-heisenberg-centers-have-infinite-centralizer-rank
kind: claim
title: A Heisenberg center or Baumslag--Solitar base in the binary Leavitt unit group has a centralizer of infinite rank over its own Laurent ring
distinct_from:
  leavitt-free-group-leading-term-forces-linear-depth: that is a metric criterion through depth growth; this is an algebraic necessary condition through determinants over the fraction field of the center.
  leavitt-north-south-thompson-unit-has-cyclic-centralizer: that computes one centralizer exactly; this shows what any Heisenberg center's centralizer must look like.
---

**ESTABLISHED** by `leavitt-heisenberg-centers-have-infinite-centralizer-rank-proof`.

Let `R = L_(F_2)(1,2)` and `Q = R^x`. For `u` in `Q` of infinite order let `C_u = C_R(u)` and
`rho(u) = dim_(F_2(u)) F_2(u) ⊗_(F_2[u]) C_u`, the **centralizer rank**. Elements killed by some nonzero
`p(u)` do not count, and `rho(u) >= 1`.

**Claim.**
- (i) If `c = [a,b]` has infinite order and commutes with `a, b in Q`, then `rho(c) = ∞`.
- (ii) In that case the group algebra `F_2[H_3(Z)]` embeds in `R`. Conversely such an embedding gives
  `H_3(Z) <= Q`. So `H_3(Z) <= Q` iff `F_2[H_3(Z)]` embeds in `L_(F_2)(1,2)`.
- (iii) If `t x t^(-1) = x^k` in `Q` with `|k| >= 2` and `x` of infinite order, then `rho(x) = ∞`.

**Examples.**
- `rho = 1` for the north--south unit (`leavitt-north-south-thompson-unit-has-cyclic-centralizer`).
- `rho(phi^j(c)) = 4^j` for its diagonal copies.
- Exact linear algebra on MSI finds `dim(C_R(u) ∩ R_4)` equal to the span of the powers of `u` for four random
  infinite-order units (`research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`, Section 3).
