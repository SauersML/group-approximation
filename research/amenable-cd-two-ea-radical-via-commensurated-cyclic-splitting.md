---
rg: 2
id: amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting
kind: route
title: A commensurated cyclic subgroup splits a cd-2 group over cyclic groups, and an amenable tree action with cyclic stabilisers is solvable; an EA radical yields such a subgroup
target: amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
requires:
  - hillman-linnell-finite-hirsch-length-theorem
  - amenable-cd-two-solvable-iff-coherent-rational-group-algebra
  - amenable-fp-iff-affiliated-top-homology-vanishes
---

Let `G` be finitely generated amenable with `cd G = 2`. Then `G` is torsion-free. By
`amenable-cd-two-solvable-iff-coherent-rational-group-algebra` (item 1 and its proof: Gildenhuys'
classification), a virtually solvable such `G` is solvable and `≅ BS(1,m)` with `m != 0`. Here
`BS(1,1) = Z²` and `BS(1,-1)` is the Klein bottle group. So in items 1-2 it suffices to prove
that `G` is virtually solvable.

## Cited theorems

- **(K) Kropholler 1990 / Margolis.** P. H. Kropholler, "Baumslag-Solitar groups and some other
  groups of cohomological dimension two", Comment. Math. Helv. 65 (1990), 547-558, proves the case
  `H` infinite cyclic. The general statement, quoted from A. J. Margolis, "Groups of cohomological
  codimension one", arXiv:1908.08826, the theorem following Theorem `main vfp`: "Let `G` be a
  finitely generated group of cohomological dimension `n+1` and let `H` [almost normal in] `G` be a
  duality group of dimension `n`. Then `G` splits as a graph of groups in which every vertex and
  edge group is commensurable to `H`." Margolis' introduction: "Kropholler proved a special case of
  this theorem when `H` is infinite cyclic". "Almost normal" means commensurated. By Margolis'
  Theorem `mainintro`, the graph is finite.
- **(T) Amenable tree actions.** Let an amenable group act on a tree without inversions. Then it
  fixes a vertex, or it fixes an end, or it preserves a pair of ends. Otherwise there are two
  hyperbolic elements with disjoint fixed-end sets, and a ping-pong power argument gives `F_2`
  (J. Tits; C. Pays and A. Valette, "Sous-groupes libres dans les groupes d'automorphismes
  d'arbres", Enseign. Math. 37 (1991)). A finitely generated group all of whose elements are
  elliptic fixes a vertex (J.-P. Serre, *Trees*, I.6.5, Corollary 3).
- **(HL)** `hillman-linnell-finite-hirsch-length-theorem`, together with Hillman (J. Austral. Math.
  Soc. Ser. A 50 (1991), Lemma 2). An elementary amenable group of finite cohomological dimension is
  torsion-free of finite Hirsch length `h`, with `h <= hd`, hence virtually solvable.
- **(GS)** D. Gildenhuys and R. Strebel; R. Bieri, *Homological dimension of discrete groups*,
  Theorem 7.10. A countable torsion-free abelian group of rank `n` has cd `n` if finitely
  generated and `n+1` otherwise.

## Item 1

Let `H = <h>` be commensurated in `G`. `H` is a duality group of dimension 1 (`PD¹`), and `cd G = 2`.
By (K), `G` is the fundamental group of a finite graph of groups whose vertex and edge groups are
commensurable to `H`. They are torsion-free and virtually `Z`, hence infinite cyclic. Let `T` be
the Bass--Serre tree. `G` acts on `T` without inversions and with infinite cyclic vertex
stabilisers.

- **`G` fixes a vertex.** Then `G` equals a vertex stabiliser `≅ Z`, contradicting `cd G = 2`.
- **Otherwise.** By (T) some subgroup `G_0` of index at most 2 fixes an end `ω` of `T`: it is `G`
  if an end is fixed, and the stabiliser of both ends of an invariant pair otherwise. `G_0` is
  finitely generated and has no fixed vertex (a fixed vertex of `G_0` would give `G` virtually `Z`).
  So by Serre it contains a hyperbolic element.
  - The Busemann function at `ω` defines a homomorphism `β: G_0 → Z`. `β(g)` is the displacement
    of `g` along rays to `ω`. `β` is nonzero on hyperbolic elements, because a hyperbolic element
    fixing `ω` has `ω` as an end of its axis.
  - Every `g ∈ L = ker β` fixes a subray of every ray to `ω`. Finitely many elements of `L` fix a
    common subray, since subrays to `ω` intersect in a subray. So every finitely generated subgroup
    of `L` lies in an edge stabiliser `≅ Z`.
  - Thus `L` is torsion-free and locally cyclic, hence abelian.
  - `G_0 = L ⋊ Z` is solvable, so `G` is virtually solvable.

## Item 2

Let `1 != N ⊴ G` be elementary amenable. `cd N <= 2`, so by (HL) `N` is torsion-free, virtually
solvable, of Hirsch length `h(N) <= 2`.

**A nontrivial abelian normal subgroup.** Let `S ⊴ N` be a solvable normal subgroup of finite
index (the normal core of a solvable subgroup of finite index). `S != 1` because `N` is infinite.
- The last nontrivial term `B` of the derived series of `S` is abelian and characteristic in `S`,
  so it is normal in `N`.
- The Hirsch--Plotkin radical `A = HP(N)` is characteristic in `N`, hence normal in `G`, and
  contains `B != 1`.
- `A` is abelian. Every finitely generated subgroup `F` of `A` is a torsion-free nilpotent group
  with `h(F) <= h(N) <= 2`. If `F` were non-abelian, `Z(F)` would have rank at least 1 and
  `F/Z(F)` would be torsion-free (upper central factors of a torsion-free nilpotent group are
  torsion-free) and non-cyclic, of rank at least 2, giving `h(F) >= 3`. So `A` is locally abelian,
  hence abelian.

So `A` is a nontrivial torsion-free abelian normal subgroup of `G` of rank `r`. Since
`cd A <= 2`, (GS) gives `r = 1`, or `r = 2` and `A ≅ Z²`.

- **`r = 1`.** Pick `1 != a ∈ A`. For `g ∈ G`, `<a>` and `<gag^-1>` are nontrivial subgroups of
  the rank-1 torsion-free abelian group `A`, so they are commensurable. Hence `<a>` is commensurated
  in `G`, and item 1 applies.
- **`r = 2`, `A ≅ Z²`.** Conjugation gives `ρ: G → GL_2(Z)`.
  - If `ρ(g)` has infinite order, then no power `g^k` (`k != 0`) lies in `A`, since elements of
    `A` act trivially. So `<A, g> ≅ Z² ⋊_{ρ(g)} Z` is poly-`Z` of Hirsch length 3 and has cd 3.
    This is impossible inside `G`.
  - So `ρ(G)` is a torsion subgroup of `GL_2(Z)`. It meets a torsion-free subgroup of finite index
    (which exists since `GL_2(Z)` is virtually free) trivially, so it is finite.
  - Hence `C = C_G(A)` has finite index in `G`. `C` is finitely generated, amenable, of cd 2, and
    `A` is central in `C`.
  - Any `1 != a ∈ A` generates a normal, hence commensurated, infinite cyclic subgroup of `C`. By
    item 1, `C` is virtually solvable, and so is `G`.

In both cases `G ≅ BS(1,m)`.

## Item 3

**The splitting.** Let `G = K*_φ = <K, t | t k t^-1 = φ(k)>` with `φ: K → K` injective and `K`
finitely generated. For a finitely generated group, such splittings with `K ⊆ ker χ` correspond to
the discrete characters `χ` with `χ` or `−χ` in `Σ¹(G)`, the sign depending on convention
(Bieri--Neumann--Strebel, Invent. Math. 90 (1987), Section 4; R. Strebel, "Notes on the Sigma
invariants", arXiv:1204.0214, Part 1). Only the splitting is used below.

**`K` is a counterexample.** `K` is amenable with `cd K <= 2`.
- If `cd K <= 1`, then `K` is free and amenable, so `K ∈ {1, Z}`, and `G ≅ Z` or `G ≅ BS(1,m)`.
- If `cd K = 2` and `K` is solvable, then `K ≅ BS(1,m)` is of type `FP_2`. The HNN extension of an
  `FP_2` vertex group along the finitely generated edge group `K` is `FP_2`. This is the
  Mayer--Vietoris sequence of the Bass--Serre tree, `0 → Z[G] ⊗_K Z → Z[G] ⊗_K Z → Z → 0`, with
  Bieri's criterion for `FP_n` of extensions. By `amenable-fp-iff-affiliated-top-homology-vanishes`,
  item 4, `G ≅ BS(1,m)`, which is solvable.

So if `G` is not solvable, `K` is fg, amenable, of cd 2 and not solvable.

**Calibration for the closing paragraph of the claim.** For `Z≀Z = <a, t>` with `χ(t) = 1`,
`χ(a) = 0`, the kernel is the module `Z[t^{±1}]`. It is not finitely generated over `Z[t]` or over
`Z[t^-1]`, so by Bieri--Strebel's metabelian criterion both `±χ ∉ Σ¹`, although `Z≀Z` is
amenable. The implication "no `F_2` ⇒ `Σ¹ ∪ −Σ¹ = S(G)`" uses finite presentability through the
Bieri--Strebel splitting theorem, and a two-dimensional counterexample is not `FP_2`.
