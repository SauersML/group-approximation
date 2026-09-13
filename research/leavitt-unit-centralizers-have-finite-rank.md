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
- **Linear annulus units (lane `ex2-q34-commuting-units`).** `rho = 1` for every north--south annulus unit
  (`leavitt-annulus-north-south-units-have-cyclic-centralizers`). This covers linear twists `c(w + 1 - 1_([10]))`
  with `w` a unit of the corner at `[10]`.
  - The point dynamics is replaced by clean prefix germs `u s_ζ = s_(ζγ)`, `t_(ζγ) u = t_ζ` at both ends.
  - The linear middle only has to permute clopen annuli.
- **Germ map.** At one clean attracting germ, `g -> t_ζ g s_ζ` gives an `F_2[u^(+-1)]`-linear map
  `C_R(u) -> F_2[t^(+-1)]`. It bounds the rank seen at that germ by `1`, and says nothing about elements with
  zero germ there.
- **Persistent leading terms.** They give an attracting ray for the leading part only. Lower terms exit and
  return, so the germ map is unavailable. This is where the extension stops
  (`research/artifacts/leavitt-annulus-north-south-centralizer-2026-09-13.md`, Section 6).

**Exact data.** For four random infinite-order units of depth 2 or 3, `dim(C_R(u) ∩ R_4)` equals the dimension
of the span of the powers of `u` in `R_4`, so the centralizer is `F_2[u^(+-1)]` up to depth 4. The diagonal copy
`phi(A)` gives the factor 4 (`research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`, Section 3).
- A screen of 2584 units with no order `<= 64` found 218 with excess centralizer in `R_3`.
- In four probed cases the excess grows like `4^N`.
- For eight excess units, the span of `u^i (C_R(u) ∩ R_3)` grows by exactly 1 per power over `i <= 12`, and most
  excess basis vectors have finite `u`-orbits. So the excess is `F_2[u]`-torsion and the observed rank is 1, even
  for units with no invariant diagonal idempotent.
- A unit with exponentially growing torsion-free centralizer would be the first candidate Heisenberg center. None
  was found.

**Why rank rather than dimension.** Parts of `R` on which `u` has finite order give huge centralizers, for
example all of a corner where `u = 1`. These are `F_2[u]`-torsion and do not count toward `rho`.
