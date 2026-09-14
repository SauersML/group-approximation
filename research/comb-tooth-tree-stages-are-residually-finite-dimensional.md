---
rg: 2
id: comb-tooth-tree-stages-are-residually-finite-dimensional
kind: claim
title: The tooth-tree stages ((U ⊕ M_d) *_{C²} M_r) * C(T) of the Popa comb plan are residually finite-dimensional whenever U is separable and RFD, and every finite-dimensional representation with the forced rank ratio extends
distinct_from:
  li-shen-amalgamated-rfd-criterion: that is the general criterion over finite-dimensional amalgams; this applies it to the stages of the comb plan, where both factors admit compatible rank ratios.
  weakly-dense-popa-combs-exist-in-property-t-factors: that is the open existence claim; this settles only its missing input 1.
---

**ESTABLISHED, unreviewed (sk-rfd-amalgam, 2026-09-14).**

Setup:
- `U` is a separable unital RFD C*-algebra, `d ≥ 1`, `r ≥ 2`, and `V = U ⊕ M_d` with tooth `e = (0,1)`. For `r = 1` the map `C² → M_1` is not injective, so it is not an embedding.
- `p ∈ M_r` is a rank-one projection.
- `C² → V` sends `(1,0) ↦ 1−e`, `(0,1) ↦ e`; `C² → M_r` sends `(1,0) ↦ 1−p`, `(0,1) ↦ p`.

Then:
1. `V *_{C²} M_r` is RFD, and so is `U^+ = (V *_{C²} M_r) * C(T)`.
2. In every finite-dimensional representation of `U^+`, `rank(e) : rank(1−e) = 1 : r−1`.
3. A finite-dimensional representation `σ` of `V` extends to `U^+` iff `dim σ(1−e) = (r−1)·dim σ(e)`, and every unitary can serve as the image of the free unitary.

By induction, every stage `U_i` of the tooth tree in `research/artifacts/sk-popa-lgx-2026-09-13-part1.md` §3 is RFD. This is missing input 1 of `weakly-dense-popa-combs-exist-in-property-t-factors`.

Route: `comb-tooth-tree-stages-rfd-via-li-shen`.

## Scope
- This does not produce the comb and says nothing about property (T) factors by itself. Missing inputs 2 (scheduling tail representations across stages inside the factor) and 3 (exact translate relations in `M`) stay open.
- Model test: Li–Shen Example 1, `M_2 *_{C²} M_3` with rank-one projections, is not RFD. There each factor has a single irreducible representation, which forces the ratios 1/2 and 1/3. In `V = U ⊕ M_d` the two summands carry independent multiplicities, so the ratio `1/r` is always reachable.
