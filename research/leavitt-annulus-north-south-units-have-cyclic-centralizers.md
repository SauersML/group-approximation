---
rg: 2
id: leavitt-annulus-north-south-units-have-cyclic-centralizers
kind: claim
title: Linear north--south annulus units of the binary Leavitt algebra, including linear twists of the Thompson unit c, have centralizer F_2[u^(+-1)]
distinct_from:
  leavitt-north-south-thompson-unit-has-cyclic-centralizer: that treats the Thompson unit c; this treats every unit with clean prefix attraction and repulsion and a linear middle, a class containing non-Thompson units such as c(1 + n) with n nilpotent in s_10 R t_10.
  leavitt-unit-centralizers-have-finite-rank: that is the open conjecture for all infinite-order units; this proves rank one for the annulus class.
artifacts:
  - research/artifacts/leavitt-annulus-north-south-centralizer-2026-09-13.md
---

**ESTABLISHED** by `leavitt-annulus-north-south-units-have-cyclic-centralizers-proof` (unreviewed).

Let `R = L_(F_2)(1,2)` and `Q = R^x`. A unit `u` is a **north--south annulus unit** if it comes with the
following data:
- words `ζ, γ, ξ, δ`, with `γ, δ` nonempty and `[ζ] ∩ [ξ] = ∅`;
- `m >= 1`, and clopen sets `D_(-m+1), ..., D_(-1)`.

Put `D_k = [ζγ^k] \ [ζγ^(k+1)]` for `k >= 0` and `D_(-m-j) = [ξδ^j] \ [ξδ^(j+1)]` for `j >= 0`. The data must
satisfy:
- `u s_ζ = s_(ζγ)` and `t_(ζγ) u = t_ζ`;
- `u^(-1) s_ξ = s_(ξδ)` and `t_(ξδ) u^(-1) = t_ξ`;
- `X = {ζγ^∞, ξδ^∞} ⊔ ⊔_k D_k`;
- `u 1_(D_k) u^(-1) = 1_(D_(k+1))` for `-m <= k <= -1`.

For every such `u` and every `a != 0`:
1. `C_R(u^a) = F_2[u, u^(-1)]`, a Laurent polynomial ring;
2. `C_Q(u^a) = <u>`.

The same holds for all `Q`-conjugates.

**Examples.**
- `c = s_00 t_0 + s_01 t_10 + s_1 t_11`.
- `c (w + 1 - 1_([10]))` for any unit `w` of the corner `1_([10]) R 1_([10])`. This is not a Thompson unit for
  `w != 1_([10])`.
- Products of `c` with units supported on one annulus.

**Consequences** (artifact, Section 5).
- No element of infinite order of a subgroup `H_3(Z) <= Q` is conjugate to an annulus unit.
- No base of a `BS(1,k) <= Q` with `|k| >= 2` is.
- In any unital embedding `f : L ⊗ L -> L`, no `f(g ⊗ 1)` or `f(1 ⊗ g)` is.
- Every commuting pair containing a conjugate of an annulus unit is algebraically dependent. This is a case of
  `leavitt-commuting-units-are-algebraically-dependent`.

**Scope.** Only clean prefix germs are used. A unit with a persistent free-group leading term has an attracting
ray for its leading part only. Its lower terms exit and return to that ray, and the argument does not reach it
(artifact, Section 6).
