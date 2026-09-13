---
rg: 2
id: radu-horizontal-quotient-is-arithmetic-lattice-proof
kind: route
title: Split the quaternion algebra at the second prime, find the S_3-fixed vertex and an inversion, and apply Bass-Serre covering to get transitivity, faithfulness and cocompactness
target: radu-horizontal-quotient-is-arithmetic-lattice
requires:
  - radu-horizontal-quotient-is-quaternionic-s-arithmetic
artifacts:
  - research/artifacts/radu-second-tree-check.py
  - research/artifacts/radu-second-tree-part2.py
  - research/artifacts/radu-second-tree-checks-output-2026-09-13.txt
  - research/artifacts/radu-valuations-check.py
  - research/artifacts/radu-valuations-checks-output-2026-09-13.txt
---

# Proof

**Part 1: a matrix model of `B` at `𝔮'`.** The script computes, exactly over `F`:
* the structure constants of `B` in the basis `e = (1, g, h, gh)`;
* the conjugation automorphism `C_s` of `B` for each word `s` in `x, y, z`;
* the element `β_s ∈ B`, unique up to `F^×`, with `β_s e_i = C_s(e_i) β_s` (the one-dimensional
  null space of a 16×4 linear system; Skolem–Noether gives existence).

At `𝔮'` put `w = 2u` with `4u^2 − u − 1 = 0`, a simple 2-adic root, computed to precision `2^70`.
The script finds `n ∈ B ⊗ Q_2` with `nrd(n) ≡ 0 mod 2^71`, takes the left ideal `B n`
(2-dimensional), and represents `β_s` by left multiplication on it. This gives matrices
`M_s ∈ GL_2(Q_2)` realizing `PB^×(F_(𝔮')) ≅ PGL_2(Q_2)`. As checks, `M_(xz) ~ M_x M_z` and
`M_(xyx) ~ M_x M_y M_x` up to scalars, and `M_(xz)^2` and `M_(xyz)^3` are scalar.

**Part 2: the vertex `p`.** A vertex of `T'` is a homothety class of lattices `P Z_2^2`, and
`d(PZ_2^2, P'Z_2^2) = v(det N) − 2 min v(N_ij)` with `N = P^(-1)P'`. Breadth-first search to
radius 12 from `Z_2^2` enumerates 12286 vertices. Exactly one of them, `p`, at distance 1,
satisfies `d(p, M_(xz)p) = d(p, M_(xyx)p) = 0`. On the three edges at `p`, `M_(xz)` acts as
`(1 2)` and `M_(xyx)` as `(0 2)`, which generate `S_3`. `M_x` and `M_z` map `p` to the neighbour
on edge 0 and back, so they invert that edge. All distances involved are integers at most 12,
far below the precision.

**Part 3: transitivity.** Let `G = ρ(V) >= <S_3, ρ(x)>`. `G·p` contains the endpoint of edge 0,
and `S_3 <= G_p` moves edge 0 to the other two edges. So every neighbour of `p` lies in `G·p`.
Since `G·p` is `G`-invariant and `T'` is connected, `G·p` is all vertices. This is item 1.

**Part 4: faithfulness.** `W = <x,y,z | x^2,y^2,z^2,(xz)^2,(xyz)^3>` is the Coxeter group on
`x, s = xz, u = xyx` with `(xs)^2 = (us)^3 = 1` and no relation between `x` and `u`. So
`W = <x,s> *_(<s>) <s,u> = D_2 *_(C_2) S_3`, and `ρ` factors through `W` by
`radu-horizontal-tree-group-is-linear`. `W` acts on its Bass–Serre tree `T_W` (3-regular after
forgetting midpoints). The equivariant map `T_W → T'`, sending the `S_3`-vertex to `p` and the
`D_2`-midpoint to the midpoint of edge 0, is locally bijective:
* at `p`, `S_3/C_2` is in bijection with the edges at `p`;
* at the midpoint, `D_2/C_2` swaps its ends.

Here `C_2 = <xz>` fixes edge 0. A locally bijective map of trees is an isomorphism. `PGL_2(Q_2)`
acts faithfully on `T'`, and `W` acts faithfully on `T_W`, since `<xz>` is not normal in `S_3`.
So `W → ρ(V)` is injective, and `Λ_v = ker(V → W)` is the normal closure of `(xz)^2` and
`(xyz)^3`. This is item 2.

**Part 5: lattice.** `ρ(A)` is simply transitive on the vertices of `T_h`, and
`Stab_Q(v_0) = ρ(V)` is transitive on the vertices of `T'`, so `Q` is transitive on the vertices
of `T_h × T'`. The stabilizer of `(v_0, p)` is `ρ(V)_p`. It is finite, since `Q` is discrete; it
acts faithfully on the edges at `p`, as `W` does on `T_W`; and it contains `S_3`. So it is `S_3`.
A discrete subgroup with finitely many orbits on vertices is a cocompact lattice. `N(O)/F^×` is
discrete, so it is a lattice containing `Q`, and the index is finite. The Euler characteristic
follows from the horizontal splitting `Q = ρ(V) *_(ρ(V_a)) ρ(E_a)` with `[ρ(V) : ρ(V_a)] = 3`:
`χ(Q) = χ(W) − χ(W)·3/2 = −χ(W)/2 = 1/24`, using `χ(W) = 1/4 + 1/6 − 1/2 = −1/12`. This is
item 3.

**Part 6: item 4.** `radu-valuations-check.py` computes `tr^2/det` exactly in `F`. For `ab`,
`bc`, `ca` it gives `1 + w/2`, whose valuation at `w = 2u` is 2. For semisimple `g` in
`PGL_2(Q_2)`, `g` fixes a vertex or an edge midpoint iff `v(tr^2 g/det g) >= 0`. Serre's lemma
(*Trees*, Chapter I, §6.5): if the generators and their pairwise products of a finitely
generated group acting on a tree all have fixed points, the group has a fixed point. ∎
