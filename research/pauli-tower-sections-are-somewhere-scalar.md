---
rg: 2
id: pauli-tower-sections-are-somewhere-scalar
kind: claim
title: In the Pauli-holonomy tower of M_2-bundles over products of real projective spaces, every self-adjoint section of every tail is somewhere scalar
distinct_from:
  some-tensor-tower-has-unsplittable-tails: that asks for towers of vector bundles whose tails have no soft half splitting; this proves the stronger scalar-point statement for a tower of twisted M_2-bundles, which are not End of any vector bundle.
  tensor-tower-bundle-trivial-iff-tails-softly-split: that is the soft-splitting criterion for tensor towers; this is a topological theorem about one explicit twisted tower that fails the criterion at every depth.
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-part2-2026-09-13.md
---

**Statement (unreviewed).** Put `d_j = 2^{j−1}` and `Y_k = RP^{d_{2k−1}} × RP^{d_{2k}}`. Let
`B_k = (S^{d_{2k−1}} × S^{d_{2k}}) ×_{(Z/2)²} M_2` be the flat `M_2`-bundle whose two antipodal
generators act on `M_2` by `Ad X` and `Ad Z` (Pauli matrices). For `0 ≤ n < m` put
`B_{n,m} = ⊠_{n<k≤m} B_k` over `Z_{n,m} = Π_{n<k≤m} Y_k`. Then every self-adjoint continuous
section `h` of `B_{n,m}` has a point `z` with `h(z) ∈ R·1`.

**Mechanism.**
- The traceless self-adjoint part of `B_{n,m}` is the direct sum, over all nonzero characters `χ` of
  `(Z/2)^{2(m−n)}`, of the real line bundles spanned by the Pauli strings. Each nonzero character
  occurs exactly once.
- `w_1` of the line for `χ` is `χ(t)`, with `t_j` the generator of `H¹(RP^{d_j}; F_2)`.
- So the top Stiefel–Whitney class is the product of all nonzero `F_2`-linear forms in the `t_j`.
  That is the Moore determinant `Σ_σ Π_j t_j^{2^{σ(j)}}`, whose monomial `Π_j t_j^{2^{j−2n−1}}`
  survives in `F_2[t]/(t_j^{d_j+1})`.
- A nowhere-zero section of `h − tr(h)1` would kill that class.

**Consequences.**
- `C(Z_{n,m}, B_{n,m})` has no projection other than `0` and `1`.
- **Unsplittable tails (Azumaya form).** At the scalar point of a positive contraction `h` with
  `|tr h − 1/2| ≤ ε` everywhere, `tr(h − h²) ≥ 1/4 − ε² > ε` for `ε ≤ 1/5`. So no tail has a
  `1/5`-soft half splitting. The criterion `tensor-tower-bundle-trivial-iff-tails-softly-split`
  holds verbatim for `M_w`-bundle towers, but the bundle-level conclusion is proved directly on
  `pauli-tower-bundle-has-scalar-point-property`.
- **Quadratic regime.** `dim Z_{0,m} = 4^m − 1` equals the rank of the traceless part, so the tail
  base dimension is about the square of the tail rank `2^m`.
- **Every prime (part 2, Theorem D; sketch, unreviewed).** For each prime `p`, flat `M_p`-bundles with
  clock–shift holonomy over products of lens spaces `L^{2d_j+1}` have the same property, where
  `d_j = (p − 1)p^{j−1}/2`. The mod-`p` Euler class is a unit times the `(p−1)/2`-th power of the
  Moore determinant, whose leading monomial survives.
- **The twist is essential.** For a genuine vector bundle `W` of rank `w ≥ 2`, the Euler class of
  `Herm_0(End W)` is pulled back from `H^{w²−1}(BU(w); Z)`, and it vanishes: the degree is odd if `w` is
  even, and over the maximal torus there is a trivial summand if `w` is odd. So each `B_{n,m}` has
  nonzero Dixmier–Douady class, and the vector-bundle form of `some-tensor-tower-has-unsplittable-tails`
  needs a non-primary obstruction.

Proof: route `pauli-tower-sections-are-somewhere-scalar-proof` (Sections 1–3 and 6 of the artifact).
