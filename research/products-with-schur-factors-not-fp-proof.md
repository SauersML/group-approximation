---
rg: 2
id: products-with-schur-factors-not-fp-proof
kind: route
title: Retract onto finite subproducts and count torsion in H_2
target: products-of-finite-groups-with-schur-factors-not-fp
requires: []
---

Let `G <= prod_n S_n` contain `(+)_n S_n`, with every `S_n` finite.

**Step 1: coordinate maps.** For each `n` let `iota_n : S_n -> G` be the
inclusion of the `n`-th coordinate copy. It lands in `G` because
`(+)_n S_n <= G`. Let `pi_n : G -> S_n` be the restriction of the `n`-th
coordinate projection. Then:
- `pi_n iota_n` is the identity of `S_n`;
- for `n' != n`, `pi_n iota_(n')` is the trivial homomorphism, since the copy of
  `S_(n')` has trivial `n`-th coordinate.

**Step 2: the finite sums embed in `H_2(G)`.** Apply `H_2(-; Z)`. A trivial
homomorphism factors through the trivial group, so it induces `0`. Fix `m` and
put
- `Phi_m = sum_(n <= m) (iota_n)_* : (+)_(n <= m) H_2(S_n) -> H_2(G)`,
- `Psi_m = ((pi_n)_*)_(n <= m) : H_2(G) -> (+)_(n <= m) H_2(S_n)`.

The `(n, n')` entry of `Psi_m Phi_m` is `(pi_n iota_(n'))_*`, which is the
identity for `n = n'` and `0` otherwise. So `Psi_m Phi_m` is the identity and
`Phi_m` is injective.

**Step 3: torsion count.** Each `H_2(S_n; Z)` is a finite group. This is
standard: a finite group has a free resolution that is finitely generated in
each degree, and the transfer to the trivial subgroup shows `|S_n|` annihilates
`H_k(S_n; Z)` for `k >= 1`. Suppose `H_2(G; Z)` is finitely generated. Then its
torsion subgroup `T` is finite. For every `m`, Step 2 embeds the finite group
`(+)_(n <= m) H_2(S_n)` in `T`. If infinitely many `H_2(S_n)` are nonzero, the
orders of these groups are unbounded, which contradicts finiteness of `T`. So
`H_2(G; Z)` is not finitely generated.

**Step 4: finite presentation.** Let `G = <X | R>` with `X` and `R` finite, and
let `P` be the presentation 2-complex: one vertex, `|X|` edges and `|R|`
2-cells, with `pi_1(P) = G`. Attaching cells of dimension at least `3` gives a
`K(G, 1)` with 2-skeleton `P`. The 2-cycles of that complex are the 2-cycles of
`P`, and the attached 3-cells only enlarge the boundaries. So `H_2(G; Z)` is a
quotient of `Z_2(P)`, a subgroup of `C_2(P) = Z^|R|`, hence finitely generated.
By Step 3, `G` has no finite presentation. `∎`
