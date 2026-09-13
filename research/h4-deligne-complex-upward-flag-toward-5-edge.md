---
rg: 2
id: h4-deligne-complex-upward-flag-toward-5-edge
kind: claim
title: The spherical Deligne complex of type H_4, ordered toward the edge labelled 5, is an upward flag poset
distinct_from:
  h3-deligne-complex-upward-flag-toward-5-edge: that is the proved H_3 case; this is the H_4 case, which is open.
---

Let `Λ = s_1 s_2 s_3 s_4` be the Coxeter diagram of type `H_4`, with `m_{s_1 s_2} = m_{s_2 s_3} = 3`
and `m_{s_3 s_4} = 5`. Order the types `ŝ_1 < ŝ_2 < ŝ_3 < ŝ_4`, and on the vertices of the Artin
complex `Δ_Λ` let `x < y` mean that `x, y` are neighbours with `type(x) < type(y)`. Then any three
pairwise upper-bounded vertices have a common upper bound.

The relation is a weakly graded partial order and is bowtie free
(`huang-relative-artin-complex-structure-lemmas`, items 3–4), so only upward flagness is open.
This is the `H_4` case of Conjecture `conj:compareB` of J. Huang, arXiv:2405.12068.

**Payoff.** With the known `B_n` and `H_3` cases, this claim gives contractible Artin complexes,
and so the K(π,1) conjecture, for the compact hyperbolic 4-simplex groups `[4,3,3,5]` and
`[5,3,3,5]` (route `artin-complexes-4335-5335-contractible-via-haettel-criterion`).

## Attempts

- **Known analogues.** `B_n` (Haettel, Prop 6.6 of *Lattices, injective metrics and the K(π,1)
  conjecture*); `H_3` (arXiv:2405.12068, Thm 7.1); the relative complex of `F_4` on a linear
  3-vertex subdiagram (arXiv:2405.12068, Prop `prop:F4`). None of these is `H_4`.
- **The F_4 argument does not transfer.** It realizes `A_{F_4}` as the fixed subgroup of a
  diagram involution of `A_{E_6}` (Crisp) and averages a join with its image under the
  involution. `H_4` is not the fixed-point type of a diagram automorphism of a simply-laced
  spherical diagram: those give `B_n, C_n, F_4, G_2`, while `H_3` and `H_4` come from non-symmetric
  foldings of `D_6` and `E_8`. So this proof has no direct `H_4` analogue.
- **Reduction to the bottom type** (lane z1-05-artin-kpi1, unreviewed). By
  `spherical-path-upward-flagness-reduces-to-bottom-triples` and the known `H_3` case, this claim
  is equivalent to `h4-deligne-complex-bottom-triples-have-upper-bounds`: three pairwise
  upper-bounded type-`ŝ_1` vertices (cosets of the `H_3` parabolic subgroup `A_{s_2 s_3 s_4}`)
  have a common upper bound. See route `h4-deligne-complex-upward-flag-from-bottom-triples`.
- **Method candidates for the base case.** The "large non-positively curved subcomplexes"
  method of arXiv:2405.12068 (sub-arrangements of the reflection arrangement) proved the `H_3`
  case. `H_4` has 60 reflection hyperplanes against 15 for `H_3`. Not attempted yet.
