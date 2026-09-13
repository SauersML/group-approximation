---
rg: 2
id: radu-xz-slab-is-second-tree-edge-stabilizer-proof
kind: route
title: Compute the slab letters on the edge of the second tree inverted by x, then compare vertex stabilizers on the first tree
target: radu-xz-slab-is-second-tree-edge-stabilizer
requires:
  - radu-delta-squared-orbit-is-signed-permutation-module
  - radu-horizontal-quotient-is-arithmetic-lattice
artifacts:
  - research/artifacts/radu-second-tree-slab-edge.py
  - research/artifacts/radu-second-tree-slab-signs.py
  - research/artifacts/radu-second-tree-slab-driver.py
  - research/artifacts/radu-second-tree-slab-output-2026-09-13.txt
  - research/artifacts/radu-slab-character-screen.py
  - research/artifacts/radu-slab-character-screen-part2.py
  - research/artifacts/radu-slab-character-screen-output-2026-09-13.txt
---

# Proof

**Computation.** The driver runs the landed `radu-second-tree-check.py`, which builds `ρ` in the
quaternion algebra, evaluates it at `𝔮'` to precision `2^70`, finds `p` and its three neighbours,
and records that `x` and `z` invert the same edge 0 at `p`. The two new parts then act on
`e' = {p, q}` (`q` = neighbour 0) and on the four outer vertices `p_1, p_2, q_1, q_2`. The output
(`radu-second-tree-slab-output-2026-09-13.txt`, run with python3.11 on MSI) reads

```text
a, b, c, xz, ab, bc, ca : fix p and q
x, z                    : swap p and q
perm on (p1,p2,q1,q2):  a = b = id,  c = (p1 p2),  x = (p1 q2)(p2 q1),  z = (p1 q1)(p2 q2),
                        xz = (p1 p2)(q1 q2).
```

**Item 1.**
* *Containment.* By the computation, `H_Q ⊆ S := Stab_Q(e')`.
* *Stabilizers on the first tree.* `W = Stab_Q(base_h)` acts on `T'` with `Stab_W(p) = <xz, xyx> ≅ S_3`
  (`radu-horizontal-quotient-is-arithmetic-lattice`, item 1). That group permutes the three edges at
  `p` as `S_3`, so the pointwise stabilizer of edge 0 in it has order 2. It is `<xz>`, since `xz`
  fixes edge 0. Adding the inversion `x` gives `Stab_W(e') = <x, z> = D_2`, which equals
  `Stab_(H_Q)(base_h)` by item 3 of `radu-delta-squared-orbit-is-signed-permutation-module`.
* *Equality.* `S` acts on the vertices of `T_h` with `Stab_S(base_h) = W ∩ S = D_2 ⊆ H_Q`. `H_Q` is
  transitive on the vertices of `T_h`, so every `s ∈ S` is `h·d` with `h ∈ H_Q` and
  `d ∈ Stab_S(base_h)`. Hence `S = H_Q`.
* *Edges.* `Q` is vertex-transitive on `T'` and `Stab_Q(p) ⊇ S_3` is transitive on the edges at `p`,
  so `Q` is edge-transitive and `Q/H_Q ≅ E(T')`. Composing with `Q/H_Q ≅ W/D_2` (item 3 of the
  module node) matches the coset `wD_2`, the 4-cycle at `w`, with the edge `w·e'`.

**Item 2.** `or_(e')`, `sgn_4` and `sgn_6 = or_(e')·sgn_4` are homomorphisms on `Stab_Q(e')`, since
they are signs of actions on `{p, q}`, on the outer four vertices, and on `N(e')`. By the
computation they take the values

```text
         a    b    c    x    z
or      +1   +1   +1   −1   −1
sgn_4   +1   +1   −1   +1   +1
sgn_6   +1   +1   −1   −1   −1   = ψ'.
```

Two characters agreeing on generators are equal.

**Item 3.** Substitute items 1–2 into item 3 of `radu-delta-squared-orbit-is-signed-permutation-module`.
For `g ∈ Q` and `e = g_0 e'`, the basis vector `g_0·m_0` is sent to `g g_0·m_0`. Changing the
representative `g_0` by `h ∈ Stab_Q(e')` multiplies the vector by `sgn_6(h)`, which is the stated
parity.

**Precision caveat.** Items 1–2 rest on exact identities in `F` evaluated at `𝔮'` with 70 bits.
Vertex coincidences are tested by valuations of `2×2` determinants, as in the landed
second-tree check. They are not symbolic proofs.

**Screens (context only, not used).** At degree-one primes `p ∈ {13, 19, 43, 47, 53, 59}` the images
of `H_Q` and `Q` in `PGL_2(F_p)` coincide, and `ψ'` does not descend
(`radu-slab-character-screen-output-2026-09-13.txt`).

∎
