---
rg: 2
id: radu-horizontal-tree-group-is-linear-proof
kind: route
title: Solve for PGL_2 involutions satisfying the square relations, match the 2-adic Bruhat-Tits tree with the horizontal tree, and lift congruence growth to openness
target: radu-horizontal-tree-group-is-linear
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - burger-mozes-infinitely-transitive-tree-groups
artifacts:
  - research/artifacts/radu-pgl2-representation-check.py
  - research/artifacts/radu-pgl2-2adic-check.py
  - research/artifacts/radu-pgl2-checks-output-2026-09-13.txt
---

# Proof

Write `f(m) = 2m^4 − m^3 + 2m^2 − m + 2` and let `[[p,q],[r,t]]` act on `P^1` by `u ↦ (pu+q)/(ru+t)`.

**Part 0: the 2-adic field.** Put `m = 2u`. Then `f(2u) = 2g(u)` with
`g(u) = 16u^4 − 4u^3 + 4u^2 − u + 1`. We have `g(1) ≡ 0 mod 2`, and `g'(u)` is odd, so Hensel's lemma
gives a unique `u ∈ Z_2` with `g(u) = 0` and `u ≡ 1 mod 2`. So `v_2(m) = 1`. From `g(u) = 0`,
`u ≡ 1 − 4u^2 + 4u^3 − 16u^4 ≡ 1 mod 4`, so `m^2 + m + 1 = 4u^2 + 2u + 1 ≡ 7 mod 8`. Then
`−(m^2 + m + 1) ≡ 1 mod 8` is a square of a unit `h ∈ Z_2^×`. Put `s = 2h` and `K = Q(m, s) ⊂ Q_2`,
a number field of degree at most 8. The artifact script computes `m ≡ 34 mod 64` and `h ≡ 5 mod 16`.

**Part 1: the relations.** How the matrices were found: `ρ(x)` fixes `0, ∞`, and `ρ(z)` swaps
them. `ρ(a) = (u ↦ m/u)` commutes with `ρ(x)`. `ρ(y)` is the involution with fixed points the
roots of `u^2 − su + m`, which `ρ(a)` swaps, so `ρ(a)` commutes with `ρ(y)`. Then
`ρ(b) = ρ(zaz)` commutes with `ρ(x)` automatically, and the relators `azbz` and `bycy` hold by
definition of `ρ(b)` and `ρ(c)`.
The remaining relator `cxcz`, i.e. `b(yxy)b = yzy`, says that `ρ(b)` maps the fixed pair
`{ρ(y)0, ρ(y)∞}` to `{ρ(y)1, ρ(y)(−1)}`. Comparing sums and products gives two equations in
`m, s`. Imposing `(xyz)^3 = 1`, i.e. `tr^2 = det`, gives `s^2 = −4(m^2+m+1)`. Then both equations
become `(m+1) f(m) = 0`, and `m = −1` would give `ρ(a) = ρ(xz)`.
The script `radu-pgl2-representation-check.py` verifies every relator exactly in
`Q[m,s]/(f(m), s^2 + 4(m^2+m+1))`: `a^2, b^2, c^2, x^2, y^2, z^2, axax, ayay, azbz, bxbx, bycy,
cxcz, (xz)^2, (xyz)^3` are all scalar matrices. So they hold in `PGL_2(K)`, and `ρ` is a
homomorphism. Every generator has invertible determinant: `f(0), f(−1) ≠ 0`, and
`det ρ(y) = 4(m+1)^2`.

**Part 2: integrality and the three neighbours.** Let `v_0` be the vertex `[Z_2^2]` of the
Bruhat–Tits tree `T` of `PGL_2(Q_2)`, a 3-regular tree.
* `ρ(x)`, `ρ(z)` and `ρ(y)/2 = [[h, −m],[1, −h]]` have entries in `Z_2` and unit determinants
  (`det ρ(y)/2 = (m+1)^2`, with `m + 1` odd). So `ρ(V)` fixes `v_0`.
* `ρ(a)` is integral with `det = −m` of valuation 1. It maps `Z_2^2` onto
  `mZ_2 ⊕ Z_2 ⊃ 2Z_2^2`, the neighbour of `v_0` with reduction the line `[0:1]`.
* `ρ(b) = [[0,1],[m,0]]` gives `[1:0]`.
* `ρ(c) = ρ(y)ρ(b)ρ(y)` gives `[1:1]`, since `ρ(y)/2 ≡ [[1,0],[1,1]] mod 2` sends `[1:0]` to
  `[1:1]`; the script confirms this.

So `ρ(a), ρ(b), ρ(c)` are involutions sending `v_0` to its three distinct neighbours.

**Part 3: the horizontal tree is `T`.** `Γ_R` acts simply transitively on the vertices of
`T_h × T_v`, with `V` the stabilizer of the root `o_h` of `T_h = Γ_R/V` and `A = <a,b,c>` the
stabilizer of the root of `T_v`. Hence `A ∩ V = 1`, `A` acts simply transitively on the vertices
of `T_h`, `Γ_R = AV`, and `a, b, c` send `o_h` to its three neighbours. Define

```text
ψ : Γ_R/V → vertices of T,     gV ↦ ρ(g) v_0.
```

It is well defined because `ρ(V)` fixes `v_0`, it is `Γ_R`-equivariant, and it maps the edge
`{gV, ghV}`, `h ∈ {a,b,c}`, to the edge `{ρ(g)v_0, ρ(g)ρ(h)v_0}`. Its restriction to `A·o_h` is
`α ↦ ρ(α)v_0`. The Cayley graph of `C_2 * C_2 * C_2` maps to `T` by `w ↦ ρ(w)v_0`. This map is
locally bijective at every vertex by Part 2 and equivariance, so it is a covering of a tree by a
tree, hence an isomorphism. So `ψ` is bijective, and `ψ` is an equivariant isomorphism of trees.
`PGL_2(Q_2)` acts faithfully on `T`, so `γ` acts trivially on `T_h` iff `ρ(γ) = 1`. So
`Λ_v = ker ρ`. This is item 2.

**Part 4: openness.** `PGL_2(Q_2) → Aut(T)` is a closed embedding, so `H_h` is the closure of
`ρ(Γ_R)` in `PGL_2(Q_2)`. `ρ(Γ_R) ∩ Stab(v_0) = ρ(V)` is dense in the open subgroup
`H_h(v_0)`, so `H_h(v_0) = closure(ρ(V)) =: H`. Let `K_n` be the kernel of
`PGL_2(Z_2) → PGL_2(Z/2^n)`; for `n >= 1`, `K_n/K_(n+1) ≅ M_2(F_2)/F_2·I` has order 8.
`radu-pgl2-2adic-check.py` computes `|H mod 2^n| = 6, 48, 192, 1536, 12288, 98304` for
`n = 1..6`. So `|H mod 16| = 8·|H mod 8|`, and `(H ∩ K_3)K_4 = K_3`.
*Lifting.* Suppose `(H ∩ K_j)K_(j+1) = K_j` with `j >= 2`. Given `g ≡ I + 2^(j+1)X` in `K_(j+1)`,
choose `h ∈ H ∩ K_j` with `h ≡ I + 2^j X mod 2^(j+1)`. Then `h^2 ≡ I + 2^(j+1)X mod 2^(j+2)`,
because `2j >= j + 2`. So `(H ∩ K_(j+1))K_(j+2) = K_(j+1)`. By induction and closedness,
`H >= K_3`. So `H_h` is open, and `[PGL_2(Z_2) : H] = |PGL_2(Z/8)|/192 = 384/192 = 2`. This is
item 4.

**Part 5: faithful vertical action.** An element of `QZ(H_h)` centralizes an open subgroup of
`PGL_2(Q_2)`. That subgroup contains some `K_n`, which is Zariski dense, so the element is central,
hence trivial. Now `Λ_h = ker(Γ_R → Aut(T_v)) = Γ_R ∩ (Aut(T_h) × 1)` is discrete and normalized by
the dense subgroup `p_h(Γ_R)`, so it is a discrete normal subgroup of `H_h`. `H_h` is closed,
non-discrete, and locally `S_3`, hence quasiprimitive. Item 2 of
`burger-mozes-infinitely-transitive-tree-groups` (Proposition 1.2.1(3)) gives
`Λ_h <= QZ(H_h) = 1`. This is item 5.

**Part 6: item 3.** `ρ(Γ_R)` is a finitely generated subgroup of `PGL_2(K)`, so it is residually
finite by Mal'cev. The finite-index normal subgroups of `ρ(Γ_R)` intersect trivially. Their
preimages are finite-index normal subgroups of `Γ_R`, so they contain `Γ_0`. Hence `ρ(Γ_0) = 1`
and `Γ_0 <= ker ρ = Λ_v`.
* *`Λ_v` is free and infinitely generated.* `V` acts simply transitively on the vertices of `T_v`,
  so `Λ_v <= V` acts freely on vertices. An element of `V` inverting an edge is a conjugate of
  `x`, `y` or `z`, and these do not lie in `ker ρ` because `ρ(x), ρ(y), ρ(z)` are not scalar. So
  `Λ_v` acts freely on the tree `T_v` and is free. It is nontrivial (it contains `(xz)^2`),
  normal, and of infinite index in the virtually free group `V`, since `ρ(xy)` has infinite order:
  `tr^2/det = 4(m^2+m+1)/(m+1)^2 = 2 + 2cos θ` with `2cos θ = (−1 ± √17)/4`, not an algebraic
  integer. A nontrivial normal subgroup of infinite index in a nonabelian free group is infinitely
  generated. Apply this to a free finite-index subgroup of `V`.
* *`T_v/Λ_v` is a Cayley graph.* `V` acts simply transitively on the vertices of `T_v` with
  `x, y, z` giving the edges at the root, so `T_v` is the Cayley graph of `V` and
  `Λ_v\T_v = Cay(ρ(V); x, y, z)`. `ρ(V)` satisfies `(xz)^2 = (xyz)^3 = 1`, so it is a quotient of
  that Coxeter group.
* *`Γ_R` is the lift group.* The lifts of any `q ∈ Q` to `T_h × T_v` form one coset of the deck
  group `Λ_v`, and `Γ_R` contains one of them.

∎
