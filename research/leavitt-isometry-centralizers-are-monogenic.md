---
rg: 2
id: leavitt-isometry-centralizers-are-monogenic
kind: claim
title: In L_k(1,n) the centralizer of a monomial isometry s_w is the polynomial ring k[s_u] on its primitive root
distinct_from:
  leavitt-annulus-north-south-units-have-cyclic-centralizers: that computes centralizers of a class of units; this computes centralizers of the non-invertible monomial isometries s_w and co-isometries t_w, which no unit statement covers.
  leavitt-unit-centralizers-have-finite-rank: that is the open rank conjecture for unit centralizers; this is a complete rank-one computation for monomial isometries, with a free-algebra proof.
  leavitt-commuting-units-are-algebraically-dependent: that is the open pair statement for units; this settles only the pairs one of whose members is a monomial isometry or co-isometry.
artifacts:
  - experiments/leavitt-commutant-scout-2026-09-17/l2.py
  - experiments/leavitt-commutant-scout-2026-09-17/commutant.py
  - experiments/leavitt-commutant-scout-2026-09-17/check_isometry_commutants.py
---

**ESTABLISHED** by `leavitt-isometry-centralizers-are-monogenic-proof` (unreviewed).

Let `k` be any field, `n >= 2`, and `L = L_k(1,n)` with generators `s_i, t_i` (`t_i s_j = δ_ij`,
`Σ_i s_i t_i = 1`). For a nonempty word `w` put `s_w = s_(w_1) ... s_(w_l)` and `t_w = (s_w)^*`, so that
`t_w s_w = 1`. Write `w = u^m` with `u` primitive. Then:
1. `C_L(s_w) = k[s_u]`, a polynomial ring in one variable;
2. `C_L(t_w) = k[t_u]`.

**Consequence.** Take commuting `a, c` in `L` with `a = s_w` or `a = t_w`. Then `c` is a polynomial in `a`'s
primitive root. In particular `a` and `c` satisfy a nonzero polynomial relation, since both lie in `k[s_u]`,
which has transcendence degree 1. So no embedding of `k[x, y]` into `L`, and in particular no embedding of
`k[Z^2]` into a corner `eLe`, can send a generator to a monomial isometry or co-isometry. The same holds after
conjugating by a unit of `L`.

An exact finite check over `F_2` (`experiments/leavitt-commutant-scout-2026-09-17/check_isometry_commutants.py`)
agrees with this. In the box of depth-2 tables with outputs of length at most 4, the commutant is spanned by the
powers of the primitive root that fit in the box:
- `C(s_0)` by `1, s_0, s_0^2`, and `C(t_0)` by `1, t_0, t_0^2`;
- `C(s_01)` and `C(s_0101)` both by `1, s_01`, and `C(t_01)` and `C(t_0101)` both by `1, t_01`.

For `w = 0101` the box contains `s_01` but not `s_w` itself, so the root `u = 01` shows up directly.
