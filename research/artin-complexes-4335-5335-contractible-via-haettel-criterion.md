---
rg: 2
id: artin-complexes-4335-5335-contractible-via-haettel-criterion
kind: route
title: Haettel's criterion along the path order reduces contractibility for [4,3,3,5] and [5,3,3,5] to upward flagness in type H_4
target: artin-complexes-of-4335-and-5335-are-contractible
requires:
  - h4-deligne-complex-upward-flag-toward-5-edge
  - h3-deligne-complex-upward-flag-toward-5-edge
  - b-n-deligne-complex-upward-flag-toward-4-edge
  - huang-relative-artin-complex-structure-lemmas
  - haettel-flag-poset-contractibility-criterion
---

Lane z1-05-artin-kpi1, 2026-09-13; unreviewed. This is the argument of Huang–Przytycki for
the rank-4 paths `434, 435, 535` (arXiv:2509.06914, proof of Lemma `lem:stpr`), run one rank
higher.

Let `Λ = s_1 s_2 s_3 s_4 s_5` with labels `(m_12, m_23, m_34, m_45) = (4,3,3,5)` or `(5,3,3,5)`.
Put `X = Δ_Λ`, types `ŝ_1 < ⋯ < ŝ_5`, and `x < y` when `x, y` are adjacent with smaller type.
For `1 ≤ i ≤ 5` let `Λ_{<i} = s_1 ⋯ s_{i−1}` and `Λ_{>i} = s_{i+1} ⋯ s_5`. We check the four
hypotheses of `haettel-flag-poset-contractibility-criterion`.

1. `X` is simply connected: structure lemma 1 with `|Λ| = 5`.
2. `<` is a partial order: structure lemma 3 with `Λ' = Λ`.
3. **Upper sets.** Let `x` have type `ŝ_i`. By structure lemma 2, `lk(x, X) ≅ Δ_{Λ−{s_i}}`, the
   join of `Δ_{Λ_{<i}}` and `Δ_{Λ_{>i}}`. Its vertices of type `ŝ_j` with `j > i` form the
   `Δ_{Λ_{>i}}` factor. Since `X` is flag, two vertices of `lk(x, X)` are adjacent in `X` iff they
   are adjacent in the link. So `V_{>x}` is the poset of `Δ_{Λ_{>i}}` ordered `ŝ_{i+1} < ⋯ < ŝ_5`,
   and `V_{≥x} = {x} ∪ V_{>x}` with `x` a minimum. Adding a minimum preserves bowtie freeness (a
   bowtie through `x` is filled by its other lower vertex) and upward flagness (a triple through
   `x` is bounded by any upper bound of the other two). Case by case:
   - `i = 1`: `Λ_{>1} = [3,3,5] = H_4`, ordered toward the 5-edge. Bowtie free by structure
     lemma 4; upward flag by `h4-deligne-complex-upward-flag-toward-5-edge`.
   - `i = 2`: `Λ_{>2} = [3,5] = H_3`, ordered toward the 5-edge:
     `h3-deligne-complex-upward-flag-toward-5-edge`.
   - `i = 3`: `Λ_{>3} = I_2(5)`. `Δ_{I_2(5)}` is a bipartite graph of girth at least 10 (Appel–Schupp
     Lemma 6, as cited in Remark `rem:easygirth` of arXiv:2509.06914). A bowtie is a 4-cycle, which
     cannot exist. Three pairwise upper-bounded vertices of the lower type with three distinct
     bounds would form an embedded 6-cycle, which also cannot exist. So two bounds coincide and
     bound all three. Triples containing a maximal vertex are bounded by it.
   - `i = 4, 5`: at most one type above `x`, nothing to check.
4. **Lower sets.** Symmetrically, `V_{≤x} = {x} ∪` the poset of `Δ_{Λ_{<i}}` ordered
   `ŝ_1 < ⋯ < ŝ_{i−1}`. Reversing the order on types gives the opposite poset, which exchanges
   downward and upward flagness and preserves bowtie freeness.
   - `i = 5`: `Λ_{<5} = [m_12, 3, 3]`. For `(4,3,3,5)` this is `B_4` with the 4-edge at the bottom;
     the opposite order runs toward the 4-edge, so downward flag follows from
     `b-n-deligne-complex-upward-flag-toward-4-edge`. For `(5,3,3,5)` it is `H_4` with the 5-edge at
     the bottom, which follows from `h4-deligne-complex-upward-flag-toward-5-edge` in the opposite
     order.
   - `i = 4`: `Λ_{<4} = [m_12, 3]` is `B_3` or `H_3` with the special edge at the bottom: `B_n` or
     `H_3` flagness in the opposite order.
   - `i = 3`: `Λ_{<3} = I_2(4)` or `I_2(5)`, of girth at least 8; same argument as in 3.
   - `i = 1, 2`: nothing to check.

By the criterion, `X` is contractible.

**Scope.** For `(4,3,3,4)` this recovers the affine `C̃_4` case. For `[5,3,3,3]` the same argument
fails at `i = 3`: `Λ_{>3} = A_2` has girth 6, and an embedded hexagon gives three pairwise
upper-bounded vertices with no common upper bound.
