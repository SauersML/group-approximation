---
rg: 2
id: leavitt-unit-centralizers-have-finite-rank
kind: claim
title: Every infinite-order unit of the binary Leavitt algebra has a centralizer of finite rank over its Laurent ring
distinct_from:
  leavitt-units-of-infinite-order-have-linear-depth-growth: that is the metric premise (depth grows linearly); this is an algebraic premise about centralizers, which excludes the same subgroups by a different mechanism.
  leavitt-heisenberg-centers-have-infinite-centralizer-rank: that proves Heisenberg centers and BS bases need infinite rank; this conjectures that no unit has it.
---

**OPEN.** Let `R = L_(F_2)(1,2)`. For every `u` in `R^x` of infinite order, the centralizer `C_R(u)` becomes a
finite-dimensional `F_2(u)`-vector space after inverting the nonzero polynomials in `u`:
`rho(u) = dim_(F_2(u)) F_2(u) ⊗_(F_2[u]) C_R(u) < ∞`.

**Payoff.** By `leavitt-heisenberg-centers-have-infinite-centralizer-rank`, this excludes `H_3(Z)` and every
`BS(1,k)` with `|k| >= 2` from `R^x` (`no-heisenberg-from-finite-centralizer-rank`). Through
`kun-thom-wreath-nonembedding-from-no-heisenberg` it also excludes every Kun--Thom wreath and double over a
Theorem E actor.

## Attempts

**Known cases.**
- `rho = 1` for the north--south unit `c = s_00 t_0 + s_01 t_10 + s_1 t_11`
  (`leavitt-north-south-thompson-unit-has-cyclic-centralizer`). That proof reads coefficients on deep
  fundamental domains near the attractor.
- `rho(phi^j(c)) = 4^j`.
- These arguments need point dynamics. For a genuinely linear unit there is no attractor, and no general
  description of `C_R(u)` is known. This is where the direct attempt stops.

**Exact data.** For four random infinite-order units of depth 2 or 3, `dim(C_R(u) ∩ R_4)` equals the dimension
of the span of the powers of `u` in `R_4`, so the centralizer is `F_2[u^(+-1)]` up to depth 4. The diagonal copy
`phi(A)` gives the factor 4 (`research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`, Section 3).
- A screen of 2584 units with no order `<= 64` found 218 with excess centralizer in `R_3`.
- In four probed cases the excess grows like `4^N`. For two of them this is explained by torsion: the unit is the
  identity on the cylinder `[00]`.
- Whether the other excess is torsion or genuine rank is open. A unit with exponentially growing torsion-free
  centralizer would be the first candidate Heisenberg center.

**Why rank rather than dimension.** Parts of `R` on which `u` has finite order give huge centralizers, for
example all of a corner where `u = 1`. These are `F_2[u]`-torsion and do not count toward `rho`.
