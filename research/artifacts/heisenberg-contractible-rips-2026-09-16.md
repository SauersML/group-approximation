# The Heisenberg group has a contractible Rips complex: an affine flag triangulation of Nil

Artifact for `heisenberg-group-has-a-contractible-rips-complex-proof`
(swarm run 2026-09-16). The finite local data is certified by
`experiments/heisenberg-contractible-rips-2026-09-16/search_h3_rips.py verify`,
with output in `verify_output.txt` in the same directory.

## Theorem

Let `H = H_3(Z)` be the set of triples `(a,b,c) ∈ Z^3` with multiplication

`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`, and `(a,b,c)^-1 = (-a,-b,-c+ab)`.

Put `x = (1,0,0)`, `y = (0,1,0)` and `z = (0,0,1) = [x,y]`. Let

`S+ = {x, y, z, xz, yz, xy, xyz} = {(1,0,0), (0,1,0), (0,0,1), (1,0,1), (0,1,1), (1,1,1), (1,1,2)}`,

and `S = S+ ∪ (S+)^-1`, which has 14 elements. Then `K = Flag(Cay(H,S))` is
homeomorphic to `R^3`. In particular the Rips complex `R_1(H, d_S)` is
contractible.

The set `S+` is the Freudenthal (Kuhn) pattern `e1, e2, e3, e1+e3, e2+e3,
e1+e2, e1+e2+e3`, with the products taken in the order `x` before `y`
before `z`.

## 1. The affine realization

`H_3(R)` is `R^3` with the same multiplication formula. `H` is a discrete
subgroup, and it acts on `R^3` by left multiplication. For `g = (p,q,r)` this
action is the affine map

`A_g(a,b,c) = (a+p, b+q, c+r+pb)`,

with linear part `[[1,0,0],[0,1,0],[0,p,1]]` of determinant `1`. Left
multiplication by a discrete subgroup of a Lie group is free and properly
discontinuous.

Define `f : |K| -> R^3` as the identity `(a,b,c) -> (a,b,c)` on vertices,
extended affinely over each simplex. Two maps `|K| -> R^3` that are affine on
simplices and agree on vertices are equal. So `f ∘ L_g = A_g ∘ f` for all
`g ∈ H`, where `L_g` is the simplicial action of `g` on `K`.

## 2. The finite local certificate

The link of the vertex `1` in `K` is `L = Flag(Γ)`, where `Γ` is the graph on
`S` with `s ~ s'` iff `s^-1 s' ∈ S`. The script checks the following by exact
integer and rational arithmetic.

- **(L1)** `Γ` has no 4-clique. Hence every simplex of `K` has dimension at
  most `3`.
- **(L2)** `L` has 14 vertices, 36 edges and 24 triangles. Every edge lies in
  exactly two triangles, the link of every vertex of `L` is a single cycle, and
  `L` is connected with `χ = 2`. So `L` is a triangulated 2-sphere.
- **(L3)** Every triangle `{s1,s2,s3}` of `L` has `det[s1,s2,s3] = ±1`, so
  every tetrahedron of `K` at `1` is non-degenerate, of volume `1/6`. For
  every edge `{s,s'}` of `L` with opposite vertices `u` and `v`,
  `det[s,s',u]` and `det[s,s',v]` have opposite signs.
- **(L4)** For the ray direction `v = (1000003, 7919, 104729)`, no cone
  `R_{>=0}·σ` over a triangle `σ` of `L` has `v` on its boundary, and exactly
  one open cone contains `v`. As a further check, 2000 random rational
  directions each lie in exactly one open cone.

The 24 triangles of `L`, as coordinate triples with `det`:

```
((-1,-1,-1),(-1,-1,0),(-1,0,-1)) +1    ((-1,-1,-1),(-1,-1,0),(0,-1,0)) -1
((-1,-1,-1),(-1,0,-1),(0,0,-1))  +1    ((-1,-1,-1),(0,-1,-1),(0,-1,0)) +1
((-1,-1,-1),(0,-1,-1),(0,0,-1))  -1    ((-1,-1,0),(-1,0,-1),(-1,0,0))  -1
((-1,-1,0),(-1,0,0),(0,0,1))     -1    ((-1,-1,0),(0,-1,0),(0,0,1))    +1
((-1,0,-1),(-1,0,0),(0,1,0))     +1    ((-1,0,-1),(0,0,-1),(0,1,0))    -1
((-1,0,0),(0,0,1),(0,1,1))       +1    ((-1,0,0),(0,1,0),(0,1,1))      -1
((0,-1,-1),(0,-1,0),(1,0,1))     -1    ((0,-1,-1),(0,0,-1),(1,0,0))    +1
((0,-1,-1),(1,0,0),(1,0,1))      +1    ((0,-1,0),(0,0,1),(1,0,1))      -1
((0,0,-1),(0,1,0),(1,1,1))       +1    ((0,0,-1),(1,0,0),(1,1,1))      -1
((0,0,1),(0,1,1),(1,1,2))        -1    ((0,0,1),(1,0,1),(1,1,2))       +1
((0,1,0),(0,1,1),(1,1,1))        +1    ((0,1,1),(1,1,1),(1,1,2))       -1
((1,0,0),(1,0,1),(1,1,2))        -1    ((1,0,0),(1,1,1),(1,1,2))       +1
```

A hand spot-check of one tetrahedron, `{1, x, xy, xyz}`:
- `x^-1 xy = y ∈ S`;
- `(xy)^-1 xyz = z ∈ S`;
- `x^-1 xyz = yz = (0,1,1) ∈ S`.

Its link triangle is `((1,0,0),(1,1,1),(1,1,2))`, with determinant
`1·(1·2-1·1) - 0 + 0 = 1`.

Volume check, not used in the proof. `H` has 6 orbits of tetrahedra
(`24/4`), each of volume `1/6`, for a total of `1`. This is the covolume of
`H` in `H_3(R)`, whose fundamental domain is `[0,1]^3`; Lebesgue measure is
invariant because each `A_g` has determinant `1`.

## 3. f is a local homeomorphism

**Step 1: radial projection of the link.** By (L3), for each triangle `σ` of
`L` the vertices `f(σ)` are linearly independent. So `0 ∉ f(|σ|)`, and the
radial projection `π = f/|f| : |L| -> S^2` is injective on `|σ|`.

- Orient each triangle `(s1,s2,s3)` of `L` positively iff
  `det[s1,s2,s3] > 0`.
- By the edge condition in (L3), the two triangles on an edge induce opposite
  orientations on it. This is therefore a global orientation of the sphere
  `L`, and `π` is orientation-preserving on every triangle.
- The two triangles on an edge `{s,s'}` project to opposite sides of the great
  circle through `π(s)` and `π(s')`. Hence `π` is a local homeomorphism at
  interior points of edges.
- Around a vertex `s` of `L`, the link of `s` is a cycle by (L2), and its
  triangles project with consistent orientation.
  - Consecutive triangles around `s` share an edge at `s` and project to
    opposite sides of its great circle.
  - Both preserve orientation, so their images at `π(s)` turn in the same
    rotational sense.
  - Going once around the cycle, the images therefore wind a total angle
    `2πk` about `π(s)`, for some integer `k >= 1`.

  So `π` is locally a branched cover `w -> w^k` at `s`, for some `k >= 1`.

Thus `π` is an orientation-preserving branched covering of `S^2`.

- Call a direction *regular* if it lies in the image of no edge of `L`. The
  image of the 1-skeleton is a finite union of arcs, so regular directions are
  dense.
- Every preimage of a regular direction lies in an open triangle, where `π`
  is an orientation-preserving embedding with local degree `+1`. So for every
  regular direction the number of preimages equals the topological degree
  `deg π`, and it does not depend on the direction.
- By (L4) there is a regular direction with exactly one preimage, so
  `deg π = 1`.

At a vertex `s` with local model `w -> w^k`, every regular direction close to
`π(s)` has at least `k` preimages near `s`. So `k <= deg π = 1`. Hence `π`
is a local homeomorphism from the compact surface `|L|` to `S^2`, which is a
covering map with `deg π = 1` sheets, i.e. a homeomorphism.

**Step 2: the star of 1.** The closed star `St(1)` is the cone on `|L|`, and
`f(t·p) = t·f(p)` for `p ∈ |L|` and `t ∈ [0,1]`, since `f(1) = 0` and `f` is
affine on simplices.
- By Step 1, `f` is injective on `St(1)`.
- Its image is the star-shaped polyhedron `{t·q : q ∈ f(|L|), t ∈ [0,1]}`, in
  which every ray from `0` meets the boundary once. So the image is a
  neighbourhood of `0`, and the open star maps homeomorphically onto an open
  neighbourhood of `0`.

**Step 3: everywhere.** For `g ∈ H`, `f` restricted to the open star of `g`
equals `A_g ∘ f ∘ L_g^-1`, which is again a homeomorphism onto an open set.
The open stars of the vertices cover `|K|`. Hence `f` is a local
homeomorphism.

## 4. f is proper, hence a homeomorphism

**Properness.** Let `C = St(1)`, which is compact; then `H·C = |K|`. Take a
compact `Q ⊆ R^3`.
- `f^-1(Q)` is contained in the union of the sets `gC` with
  `A_g(f(C)) ∩ Q ≠ ∅`.
- Since `f(C)` is compact and `H` acts properly discontinuously on `R^3`, only
  finitely many `g` occur.
- So `f^-1(Q)` is closed in a finite union of compact sets, and is compact.

**Covering.** `|K|` and `R^3` are locally compact Hausdorff, and `f` is a
proper local homeomorphism. Take `y ∈ R^3`.
- `f^-1(y)` is compact and discrete, hence finite, say `{x_1,…,x_k}`.
- Choose pairwise disjoint open `U_i ∋ x_i` with `f|U_i` a homeomorphism onto
  an open set.
- Proper maps into locally compact Hausdorff spaces are closed. So
  `V = R^3 ∖ f(|K| ∖ ∪U_i)` is an open neighbourhood of `y`.
- `W = V ∩ ∩_i f(U_i)` is then evenly covered.

The image of `f` is open, since `f` is a local homeomorphism, and closed,
since `f` is proper. So `f` is surjective and hence a covering map.

**Conclusion.** `|K|` is connected, since `S ∋ x, y` generates `H`. `R^3` is
simply connected, so the covering `f` is a homeomorphism, and `|K| ≅ R^3` is
contractible. By item 1 of
`group-rips-complexes-are-cayley-graph-flag-complexes`,
`K = Flag(Cay(H,S)) = R_1(H,S)`. ∎

## Remarks

1. The search `search_h3_rips.py 7` runs over all choices of 7 inverse pairs
   from the 20 pairs of `(a,b,c)` with `|a|,|b| <= 1` and `|c| <= 2`. It finds
   20 generating sets passing (L1)–(L4). The set `S` above is one of them.
2. Sections 3–4 use only four things:
   - the finite checks (L1)–(L4);
   - an action of `G` by affine maps on `R^d` that is properly discontinuous;
   - an equivariant map on vertices;
   - a generating set `S`, so that `K` is connected.

   The same argument therefore gives a `d`-dimensional test. Here it is
   applied only to `H_3(Z)` with this `S`.
3. `H_3(Z)` is not expected to lie in the other positive classes of the
   graph, and its linear parts `[[1,0,0],[0,1,0],[0,p,1]]` are not signed
   permutations, so `linf-preserving-proper-actions-give-contractible-rips`
   does not apply to this action. The expected reasons, all standard facts
   that were not re-checked in this run:
   - A virtually nilpotent group acting geometrically on a CAT(0) space is
     virtually abelian, so `H_3(Z)` is not CAT(0).
   - Its Dehn function is cubic. Automatic groups have quadratic Dehn
     function, so it is not automatic.
   - Helly groups are biautomatic, so it is not Helly.

   The theorem does not depend on any of these facts.
4. Referee cross-check (2026-09-16), not used in the proof.
   `experiments/heisenberg-contractible-rips-2026-09-16/referee_check_h3.py`
   was written independently of the search script. It checks the following.
   - (L1)–(L3): `V,E,F = 14,36,24`, no 4-clique, all determinants `±1`,
     opposite signs across every link edge, every vertex link a cycle.
   - (L4): 3000 random integer directions off the cone boundaries each lie
     in exactly one open cone.
   - Globally: 300 random rational points of `[0,1]^3` each lie in exactly
     one affinely realized tetrahedron `g·τ`, with `g` in a box of `H`.

   Output: `referee_output.txt`.