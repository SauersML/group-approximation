---
rg: 2
id: h4-deligne-complex-bottom-triples-have-upper-bounds
kind: claim
title: In the H_4 Deligne complex ordered toward the 5-edge, three pairwise upper-bounded bottom-type vertices have a common upper bound
distinct_from:
  h4-deligne-complex-upward-flag-toward-5-edge: that is upward flagness of the whole H_4 poset; this is its bottom-type case, which implies it given the H_3 theorem.
---

Let `Λ = s_1 s_2 s_3 s_4` be of type `H_4` with `m_{s_3 s_4} = 5`, types ordered
`ŝ_1 < ŝ_2 < ŝ_3 < ŝ_4`. Let `x_1, x_2, x_3` be vertices of `Δ_Λ` of type `ŝ_1`, i.e. left cosets of
the parabolic subgroup `A_{s_2 s_3 s_4}` of type `H_3`, such that for each pair `x_i, x_j` some
vertex of higher type is adjacent to both. Then some vertex is adjacent to all three and has
higher type than `ŝ_1`.

With `h3-deligne-complex-upward-flag-toward-5-edge` and
`spherical-path-upward-flagness-reduces-to-bottom-triples`, this gives
`h4-deligne-complex-upward-flag-toward-5-edge` (route
`h4-deligne-complex-upward-flag-from-bottom-triples`).

## Attempts

- **Configuration.** Take the joins `y_{ij}` (they exist by bowtie freeness). The configuration
  is a 6-cycle `x_1 y_{12} x_2 y_{23} x_3 y_{31}` whose `y`-vertices have types among `ŝ_2`
  (cosets of `A_{s_1} × A_{s_3 s_4}`), `ŝ_3` (`A_{s_1 s_2} × A_{s_4}`) and `ŝ_4` (`A_{s_1 s_2 s_3}` of
  type `A_3`). The claim asks for a filling by three 4-cycles through one vertex. By the
  cycle-to-word translation of arXiv:2405.12068 (Definition `def:ncycle`), this is a statement
  about the products `w_1 ⋯ w_6 = 1` with `w_i` alternating between `A_{s_2 s_3 s_4}` and the
  parabolic subgroups of the `y`-types.
- **How H_3 was done.** The analogous statement for `H_3` is Lemma `lem:triple` of
  arXiv:2405.12068. It projects the 6-cycle to the Coxeter complex, cases on the image (a single
  edge, or two edges), and uses auxiliary sub-arrangements of the `H_3` arrangement whose
  complements carry CAT(0) complexes of groups, then combinatorial Gauss–Bonnet. An `H_4`
  version needs sub-arrangements of the 60-hyperplane `H_4` arrangement with the same
  properties. Not attempted.
- **Evidence search (not run).** A bounded computer search for a counterexample inside balls of
  the Garside normal form of `A_{H_4}` would test the claim, and a counterexample would refute
  the `H_4` case of Conjecture `conj:compareB` of arXiv:2405.12068. Lane rules: MSI only, small jobs.
