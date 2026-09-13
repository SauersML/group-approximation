---
rg: 2
id: leavitt-north-south-thompson-unit-has-cyclic-centralizer
kind: claim
title: A north--south Thompson unit of the binary Leavitt algebra has centralizer F_2[c^(+-1)], and <c> is an almost malnormal maximal abelian subgroup of the unit group
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is a metric theorem about V_n; this computes centralizers inside the whole Leavitt algebra, whose linear units are not homeomorphisms of the Cantor set.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that is the open Heisenberg question; this is an established partial obstruction, excluding Heisenberg centers conjugate to powers of one Thompson unit.
  binary-leavitt-full-character-simplex: that classifies characters of the unit group; this identifies an explicit maximal abelian subalgebra L(<c>) of its group von Neumann algebra.
artifacts:
  - research/artifacts/leavitt-north-south-centralizer-2026-09-12.md
---

**ESTABLISHED** by `leavitt-north-south-thompson-unit-has-cyclic-centralizer-proof`.

Let `R = L_(F_2)(1,2)` and `Q = R^x`, and let `c = s_00 t_0 + s_01 t_10 + s_1 t_11`. This
is the Thompson unit `0 gamma -> 00 gamma`, `10 gamma -> 01 gamma`,
`11 gamma -> 1 gamma`, with attracting fixed point `0^infinity` and repelling fixed point
`1^infinity`. For every `a != 0`:

1. `C_R(c^a) = F_2[c, c^-1]`, a Laurent polynomial ring in `c`;
2. `C_Q(c^a) = <c>`;
3. `g c^a g^-1 = c^b` with `g` in `Q` and `b != 0` forces `b = +-a`;
4. `[N_Q(<c>) : <c>] <= 2`, and `g <c> g^-1 cap <c> = 1` for `g` outside `N_Q(<c>)`;
5. `L(<c>)` is a maximal abelian subalgebra of `L(Q)`.

**Consequence.** Neither the central commutator of an integer Heisenberg subgroup of `Q`,
nor the base element of a Baumslag--Solitar subgroup `BS(1,k)` of `Q` with `|k| >= 2`,
is conjugate in `Q` to a power of `c`. All five items transfer to every `Q`-conjugate
of `c`.

**Why this is not a statement about V.** Inside `V` the centralizer of `c` is known
(Bleak--Bowman--Gordon--Graham--Hughes--Matucci--Sapir). Here the competitors are
arbitrary linear units, finite `F_2`-combinations of prefix replacements, which act on
functions and not on points. The proof works through the faithful action on locally
constant functions. It uses three inputs:
- a support-measure bound for elements of bounded depth;
- equivariance along the flow of `c`;
- the fact that an element of depth `N` reads only `N` letters of a point near the
  attractor.

**Scope.** The argument does not reach Heisenberg centers that are genuinely linear
units, since those have no attractor. It also shows that no `K`-theoretic determinant
can stand in for it: `K_0(R) = 0`, so the central `t` of `R[t^(+-1)]^x` is trivial in
`K_1`. See the artifact, Section 4.
