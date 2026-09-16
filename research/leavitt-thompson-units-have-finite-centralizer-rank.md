---
rg: 2
id: leavitt-thompson-units-have-finite-centralizer-rank
kind: claim
title: Every conjugate of an infinite-order Thompson unit of the binary Leavitt algebra has finite centralizer rank, bounded by its attracting periodic orbits
distinct_from:
  leavitt-unit-centralizers-have-finite-rank: that conjectures finite rank for every infinite-order unit, including genuinely linear ones with no point dynamics; this proves it only for conjugates of units coming from Thompson's group V.
  leavitt-north-south-thompson-unit-has-cyclic-centralizer: that computes the centralizer of one north--south unit exactly (rank 1); this bounds the rank for every infinite-order element of V, and the bound is not always sharp.
  leavitt-annulus-north-south-units-have-cyclic-centralizers: that gets rank 1 for north--south annulus units, including linear twists that are not Thompson units; this covers arbitrary infinite-order Thompson units, with any number of attracting orbits, and not the linear twists.
artifacts:
  - research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md
---

Let `R = L_(F_2)(1,2)` and `Q = R^x`. For `u ∈ Q` of infinite order,
`rho(u) = dim_(F_2(u)) F_2(u) ⊗_(F_2[u]) C_R(u)`.

An element `g` of Thompson's group `V`, `g(β_i z) = α_i z` for complete prefix codes, gives the **Thompson
unit** `u_g = Σ_i s_(α_i) t_(β_i)`. The map `g -> u_g` is an injective group homomorphism `V -> Q`.

**Claim.** Let `g ∈ V` have infinite order and `w ∈ Q`. Then
`1 <= rho(w u_g w^(-1)) <= min(N(g), N(g^(-1))) < ∞`.
- `N(g) = |P_a(g)| · Σ_O d_O`.
- `P_a(g)` is the set of periodic points `p`, `g^k p = p`, at which the local replacement `a z -> a' z` of `g^k`
  lengthens words (`|a'| > |a|`). It is finite and nonempty.
- `O` runs over the `g`-orbits in `P_a(g)`, and `d_O = |a'| − |a|` for `k = |O|`.

Proof: `leavitt-thompson-units-have-finite-centralizer-rank-proof`.

**Examples.**
- `N = rho = 1` for the north--south unit `c`, `N = rho = 2` for `c^2`, and `N = rho = 4` for `phi(c)`.
- The two-cycle `u = s_1 c t_0 + s_0 t_1` has `C_R(u) = F_2[u^(±1)]`, so `rho = 1`, but `N = 2`. The bound is
  not sharp.

**Consequences** (artifact, Section 4). For every infinite-order `g ∈ V` and `w ∈ Q`, `y = w u_g w^(-1)`
satisfies the following.
- Every element of `R` commuting with `y` is algebraic over `F_2[y]`. This is the `U_V` case of
  `leavitt-commuting-units-are-algebraically-dependent`.
  - When the commuting element is also a conjugate, by the same `w`, of a Thompson unit, this was already known:
    Brownlowe–Sørensen, arXiv:1603.03618, Proposition 3.4, as recorded in
    `research/artifacts/brownlowe-sorensen-transfer-to-f2-2026-09-13.md`.
- `y` is not the central commutator of a Heisenberg pair in `Q`, and not the base of a `BS(1,k)`, `|k| >= 2`,
  in `Q` (via `leavitt-heisenberg-centers-have-infinite-centralizer-rank`).
- `y` is not conjugate to `phi(y)`. This is the `U_V` case of `leavitt-units-are-not-conjugate-to-diagonal-copies`.

**Scope.** The proof uses point dynamics of `g` on `{0,1}^ω`. For linear units, which are not indicators of
bisections of the groupoid, there is no substitute. The general claim `leavitt-unit-centralizers-have-finite-rank`
stays open.

## Attempts

- 2026-09-16 (swarm lane `leavitt-unit-centralizers-have-finite-rank`). Direct proof, with full details in the
  artifact.
  - The dynamical input is that `A0 = P_0`, `B = P_r`, and that `P_a, P_r` are finite and nonempty for infinite
    order.
  - The germ map `C_R(u_g) -> ⊕_(P_a × P_a) F_2[x^(±1)]` is `F_2[u]`-linear into a free module of rank `N(g)`.
  - Its kernel is `F_2[u]`-torsion, by a compactness argument on the support in the groupoid.
- Exact linear algebra in `R_3` matches the bound for `c`, `c^2` and `phi(c)`, and shows it is not sharp for the
  two-cycle (`experiments/leavitt-thompson-centralizer-rank-2026-09-16/`).
- Open refinements: the exact value of `rho(u_g)`, and any extension to linear units.
