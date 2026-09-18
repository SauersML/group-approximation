---
rg: 2
id: bg-pattern-groups-locally-finite-host-obstruction-proof
kind: route
title: Finite a-orbits make cl<a> a compact totally disconnected subgroup of Sym(S), where the smallest-prime argument kills a; conjugacy of a with a^2 forces translation length zero, so a is elliptic on any locally finite tree or CAT(0) complex with finitely many shapes and has finite orbits on cells
target: bg-pattern-groups-act-on-no-locally-finite-cat0-complex
requires:
  - higman-group-embeds-in-no-almost-automorphism-group
---

## Item 1 (topological lemma)

Let `K = cl<a>` and `K_b = cl<b>`. Conjugation by `t` is a homeomorphism of `T`
carrying `<a>` onto `<b>`, so it carries `K` onto `K_b`, and `K_b` is compact and
totally disconnected. A compact totally disconnected Hausdorff group is
profinite, so `K ≅ K_b` are procyclic profinite groups. Let `P` be the set of
primes `p` such that `K` has a continuous quotient `Z/p`. For `m ≥ 1` put
`U_m = cl<a^m>`. If `p ∈ P` then `U_p` is the unique open subgroup of index `p`.

**Step A (positive powers recur).** In a compact group `L`, for each `x ∈ L` and
each neighbourhood `O` of `1` there are infinitely many `j ≥ 1` with `x^j ∈ O`:
choose a convergent subsequence `x^(n_i)` and take `j = n_(i+1) − n_i` for large `i`.

**Step B (`2 ∉ P`).** Suppose `2 ∈ P`. Then `a U_2` is an open subset of `K` not
containing `1`, so there is an open `O ∋ 1` in `T` with `O ∩ a U_2 = ∅`. The map
`k ↦ k a k^-1 a^-1` is continuous and sends `1` to `1`, so there is an open `V ∋ 1`
with `k a k^-1 a^-1 ∈ O` for `k ∈ V`. By Step A some `j ≥ 1` has `b^j ∈ V`, so
`b^j a b^-j a^-1 = a^(2^j − 1) ∈ O`. But `2^j − 1` is odd, so this element lies in
`a U_2`. Contradiction.

**Step C (`K_b` normalizes every `U_m`).**
- The maps `k ↦ b k b^-1` and `k ↦ k^2` are continuous endomorphisms of `K`
  (the first maps `<a>` into `<a>`, hence `K` into `K`). They agree on `<a>`, so
  they agree on `K`.
- Since `2 ∉ P`, squaring is a bijection on every finite quotient `K/U_n` of odd
  order, and every open subgroup of `K` has odd index. So squaring is a
  continuous bijection of the compact group `K` and `b K b^-1 = K`.
- Every `U_m` is characteristic among open subgroups (it is the unique one of its
  index), so `b U_m b^-1 = U_m` and `b^-1 U_m b = U_m`.
- For a closed subgroup `U`, the set `{h : h U h^-1 ⊆ U and h^-1 U h ⊆ U}` is
  closed. It is the normalizer of `U` and contains `b`, hence `K_b`.

**Step D (smallest prime).** Suppose `K ≠ 1`, so `P ≠ ∅`; let `p = min P`. By
Step B, `p` is odd. By Step C conjugation gives a homomorphism
`ψ : K_b → Aut(K/U_p) ≅ (Z/p)^×`. For `x ∈ K` the map `k ↦ k x k^-1 U_p` into
the finite discrete set `K/U_p` is continuous, so `ψ` has open kernel. Now
`ψ(b)` is multiplication by `2`, of order `o = ord_p(2) ≥ 2` since `p ≥ 3`, and
`<b>` is dense in `K_b`, so `ψ(K_b)` is cyclic of order `o`. Choose a prime
`q | o`. Then `K_b`, hence `K`, has a continuous quotient `Z/q`, so `q ∈ P`. But
`q | p − 1`, so `q < p`. Contradiction. Hence `K = 1` and `a = 1`.

## Item 2 (permutation actions)

Let `T = Sym(S)` with the topology of pointwise convergence. It is a Hausdorff,
totally disconnected topological group. Let `ā, b̄, t̄` be the images; they form a
BG pattern in `T`. Let `L ⊆ Sym(S)` be the subgroup of permutations preserving each
`<a>`-orbit. As a space `L = ∏_O Sym(O)` over the (finite) orbits `O`, with the
product of discrete topologies, so `L` is compact, and it is closed in `Sym(S)`.
It contains `<ā>`, so `cl<ā> ⊆ L` is compact and totally disconnected. By item 1,
`ā = 1`.

## Item 3 (locally finite trees)

Replace the tree by its barycentric subdivision, so that `Γ` acts without
inversions; local finiteness is kept. For an automorphism `g` without inversions
let `ℓ(g) = min_v d(v, g v)`. Then `ℓ` is a conjugacy invariant and `ℓ(g^n) = |n| ℓ(g)`
(Serre, *Trees*, I.6.4, Prop. 24–25). Since `b ā b^-1 = ā^2`, `ℓ(ā) = 2 ℓ(ā)`, so
`ℓ(ā) = 0` and `ā` fixes a vertex `v`. Then `ā` preserves each sphere around `v`,
which is finite, so every `<a>`-orbit on vertices is finite. By item 2 `a` acts
trivially on vertices, hence on the tree.

## Item 4 (locally finite CAT(0) complexes)

Let `X` be such a complex and `ā` the image of `a`. By Bridson, *On the
semisimplicity of polyhedral isometries* (Proc. AMS 127, 1999), every cellular
isometry of an `M_κ`-polyhedral complex with finitely many shapes is semisimple.
For semisimple isometries of a CAT(0) space the translation length satisfies
`|g^n| = |n| |g|` and is conjugacy invariant (Bridson--Haefliger II.6.2 and II.6.8).
So `|ā| = 2|ā|`, `|ā| = 0`, and semisimplicity gives a fixed point `x`. Let `σ`
be the open cell containing `x`; `ā` maps `σ` to itself. Cellular isometries
preserve the combinatorial distance in the cell-adjacency graph, and by local
finiteness each combinatorial ball around `σ` contains finitely many cells. So
every `<a>`-orbit on the set of cells is finite, and by item 2 `a` fixes every
cell setwise. In particular `ā` fixes every vertex. An isometry of a convex
`M_κ`-polyhedron fixing its vertices is the identity (the vertices affinely span
it in the model space), so `ā` is the identity on `X`.

A finite product of locally finite trees, with the product cell structure, is a
locally finite CAT(0) cube complex with one shape, and every automorphism of the
product (including factor permutations) is a cellular isometry. So it is a
special case.

## Item 5 (Higman's group)

By item 1 of `higman-group-embeds-in-no-almost-automorphism-group` (the profinite
four-cycle lemma): if `h_0, …, h_3` in a Hausdorff topological group satisfy
`h_i h_(i+1) h_i^-1 = h_(i+1)^2` and every `cl<h_i>` is compact and totally
disconnected, then all `h_i = 1`. The argument of item 2 applies to each `g_i`
separately in `Sym(S)`, so an action with all `g_i`-orbits finite is trivial.
Each `g_(i+1)` is conjugate to its square by `g_i`, so the translation-length
arguments of items 3 and 4 make each `g_i` elliptic, with finite orbits on vertices
or cells, and the action is trivial.

## Calibration

- Taking `S` finite in item 2 recovers that every finite image of `BG` kills `a`, and that `H4` has no nontrivial finite
  quotient.
- `BS(1,2)` acts faithfully on its locally finite Bass--Serre tree with `a`
  elliptic. There is no `t` there, and the closures of `<a>` and `<b>` in the
  tree's automorphism group are `Z_2` and a non-compact group, so the lemma does
  not apply. This matches the need for `t` in Step C–D.
- For exponent 3, `SL(2,3)` gives a pattern with `a ≠ 1` and finite orbits, so
  Step D (`ord_p(2) ≥ 2`) is where the exponent matters.
