# Brick codings die at connected corners (2026-09-17, wave 5)

This artifact extends `research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md`
(Parts A–D). Notation is as in that file and in
`brick-coded-two-graph-full-groups-embed-in-brin-thompson`. For a brick coding `φ` in
dimension `m`:

- **(B1)** at each vertex and in each colour, the bricks `[φ(e)]` of the outgoing edges
  partition `C^m`;
- **(B2)** `φ_j(e)φ_j(f) = φ_j(f')φ_j(e')` on every square `ef = f'e'`, where `e`, `e'`
  have colour 1 and `f`, `f'` have colour 2;
- **(B3)** some `N` makes every rectangle of degree `(N,N)` have a nonempty code in every
  coordinate.

**Summary.**

- **Part E** is an abstract theorem. Take the rigidity hypotheses (R1)–(R3) of
  `two-graph-brick-codings-are-rigid-under-rank-two-h1`. Add connectivity of the level-1
  *corner compatibility graphs*. Then no brick coding exists in any dimension, whatever
  the row sums are.
- **Part F** proves that connectivity for the tile 2-graph of *every* triangle
  presentation over *every* `PG(2,q)`. Each corner graph is the point–line incidence
  graph of an affine plane of order `q` with one parallel class removed.
- **Part G** gives the corollary. For every triangle presentation with unique filling
  and (R1)–(R3), the tile 2-graph has no brick coding. For the five `PG(2,2)` examples
  this replaces the SAT certificate with a pen-and-paper proof plus the exact linear
  algebra already recorded.
- **Part H** gives computations, a belief update and survivors.

## Part E. The corner theorem

**Definition.** Let `Λ` be a finite 2-graph and `a` a vertex. The *corner graph* `B_1(a)`
is the bipartite graph with vertex set `E_1(a) ⊔ E_2(a)`, the colour-1 and colour-2
edges with source `a`. It has an edge between `e ∈ E_1(a)` and `f' ∈ E_2(a)` iff some
square `ef = f'e'` exists. Such a pair is called *compatible*.

**(C1)** `B_1(a)` is connected for every vertex `a`.

**Theorem E.** Let `Λ` be a finite 2-graph in which every vertex emits edges of both
colours, satisfying (R1), (R2), (R3) and (C1). Then `Λ` has no brick coding in any
dimension `m ≥ 1`.

**Proof.** Suppose `φ` is a brick coding in dimension `m`, and fix a coordinate `j`.

*Step E1 (comparability at corners).* Let `e ∈ E_1(a)` and `f' ∈ E_2(a)` be compatible,
via a square `ef = f'e'`. By (B2) the binary words `φ_j(e)` and `φ_j(f')` are both
prefixes of the single word `φ_j(e)φ_j(f) = φ_j(f')φ_j(e')`. So one is a prefix of the
other. In particular, if both are nonempty they have the same first letter.

*Step E2 (an empty code at every vertex).* Fix a vertex `a`, and suppose every edge in
`E_1(a) ⊔ E_2(a)` has a nonempty `j`-code.

- By E1, adjacent vertices of `B_1(a)` carry codes with the same first letter.
- By (C1), `B_1(a)` is connected, so all edges at `a` have codes starting with one letter
  `c`.
- Hence every colour-1 brick `[φ(e)]`, `e ∈ E_1(a)`, lies inside
  `{x ∈ C^m : x_j ∈ cC}`.
- That set is a proper subset of `C^m`, because its complement `{x_j ∈ (1-c)C}` is
  nonempty. So the colour-1 bricks at `a` do not cover `C^m`, contradicting (B1).

Therefore every vertex `a` emits some edge `σ(a)`, of colour 1 or 2, with
`φ_j(σ(a))` the empty word.

*Step E3 (a zero-length cycle).*

- Start at any vertex and follow `σ`. Since `Λ^0` is finite, some vertex repeats.
- This gives a closed edge path `ξ = σ(a_0)σ(a_1)…σ(a_{r-1})`, with `r ≥ 1` and
  `a_{i+1} = t(σ(a_i))` (indices mod `r`).
- Let `p` and `s` be the numbers of colour-1 and colour-2 edges in `ξ`, so `p + s = r ≥ 1`.
- The code length `ℓ_j = |φ_j|` is additive along paths, so `ℓ_j(ξ) = 0`.

*Step E4 (positive slopes).*

- By (B2), `ℓ_j` is a 1-cocycle on the square complex `K(Λ)`.
- Part (b) of `two-graph-brick-codings-are-rigid-under-rank-two-h1`, which uses (R1)–(R3),
  states verbatim: "In `H^1`, every coordinate length cocycle is `ℓ_j = α_j d_1 + β_j d_2`
  with `α_j, β_j > 0`". So `ℓ_j − α_j d_1 − β_j d_2 = δg_j` for a real 0-cochain `g_j`.
- A coboundary sums to zero around a closed edge path. Hence
  `0 = ℓ_j(ξ) = α_j p + β_j s`.
- The right side is `> 0`, because `α_j, β_j > 0`, `p, s ≥ 0` and `p + s ≥ 1`.
- This contradiction proves Theorem E. ∎

**Remarks.**

1. **Where (R2)/(R3) are used.** Without (R3), the rigidity proof still gives
   `α_j, β_j ≥ 0` and `α_j + β_j > 0`, so the argument still kills a *mixed* zero cycle
   (`p, s ≥ 1`). That case can also be seen directly: `ξ^N` has an initial segment of
   degree `(N,N)` whose code is a prefix of the empty word, which contradicts (B3). A
   pure colour-1 zero cycle is excluded only by `α_j > 0`, which is where (R3) enters.
2. **Row sums play no role.** Theorem E does not use that the row sums are powers of 2.
   It kills the case `N_i = 2^α` that Corollary B2 of the earlier artifact leaves to SAT.
3. **Invariant and step.** The invariant is the connectivity of the corner compatibility
   graph. Every brick coding dies at Step E2: (B2)-comparability forces one first letter
   per coordinate at each vertex, which contradicts (B1).

## Part F. Corner graphs of triangle-presentation tile 2-graphs are affine

**Setting.**

- `PG(2,q)` is a projective plane of order `q ≥ 2`, and `λ : points → lines` is a
  bijection.
- A triangle presentation `T ⊆ P^3` satisfies, as in `tp.py`:
  - (A1) for all `x,y`, some `z` has `(x,y,z) ∈ T` iff `y ∈ λ(x)`;
  - (A2) `(x,y,z) ∈ T ⇒ (y,z,x) ∈ T`;
  - (A3) for all `x,y`, at most one `z` has `(x,y,z) ∈ T`.
- Write `I(x,y)` for `y ∈ λ(x)`. When `I(x,y)` holds, write `τ(x,y)` for the unique `z`
  with `(x,y,z) ∈ T`.
- By (A2), `(x,y,z) ∈ T` implies `I(x,y)`, `I(y,z)` and `I(z,x)`, and also
  `τ(y,z) = x` and `τ(z,x) = y`.

**The tile 2-graph `Λ_T`** is as in `rs2graph.py`.

- *Vertices* are the tiles `(x,y,z,u,w)` with `(x,y,z) ∈ T`, `(y,u,w) ∈ T` and `u ≠ z`.
- A colour-1 edge `a → b` exists iff `w_a = z_b` and `y_a ≠ x_b`.
- A colour-2 edge `a → c` exists iff `u_a = x_c` and `w_a ≠ y_c`.
- The squares are the words `(a→b→d) = (a→c→d)`, with `b→d` and `a→c` of colour 2.

(H1) is *unique filling*: for every colour-1-then-2 path `a → b → d` there is exactly
one `c` with `a -2-> c -1-> d`. `rs2graph.build` asserts it, and it is what makes `Λ_T`
a 2-graph with these squares.

**Proposition F.** Assume (A1)–(A3) and (H1). Fix a tile `a = (x,y,z,u,w)`, and let
`ℓ = λ(u)`. Then `w ∈ ℓ`, and there are bijections

- `E_1(a) → {points not on ℓ}`, sending `b` to `u_b`;
- `E_2(a) → {lines λ(p) not through w}`, sending `c` to `λ(w_c)`.

Under these bijections, `b` and `c` are compatible iff `u_b ∈ λ(w_c)`. So `B_1(a)` is
the incidence graph of the affine plane `PG(2,q) \ ℓ`, restricted to the affine lines
outside the parallel class of the point at infinity `w`. It has `q^2 + q^2` vertices, is
`q`-regular, and is connected. In particular (C1) holds for `Λ_T`, and `|E_i(a)| = q^2`,
so (R1)'s row sums are constant.

**Proof.**

*F0.* Since `(y,u,w) ∈ T`, (A2) gives `I(y,u)`, `I(u,w)` and `I(w,y)`. So `w ∈ λ(u) = ℓ`.

*F1 (colour 1).* A colour-1 edge `a → b` means `b = (x',y',w,u',w')` with:

- `(x',y',w) ∈ T` and `x' ≠ y`;
- `(y',u',w') ∈ T` and `u' ≠ w`.

From `(x',y',w) ∈ T` and (A2), `(w,x',y') ∈ T` and `(y',w,x') ∈ T`. So `I(w,x')`,
`y' = τ(w,x')`, `I(y',w)` and `x' = τ(y',w)`.

- *The map `x' ↦ y'`.* It is a bijection `{x' : I(w,x')} → {p : I(p,w)}`, with inverse
  `p ↦ τ(p,w)`.
- *The excluded value.* `x' = y` iff `y' = τ(w,y) = u`, because `(w,y,u) ∈ T`. So `y'`
  ranges over the `p ≠ u` whose line `λ(p)` passes through `w`.
- *Injectivity of `b ↦ u'`.* Given `b`, both `u'` and `w` lie on `λ(y')`, with `u' ≠ w`.
  So `λ(y')` is the line `wu'`, and `y'` is determined by `u'`. Then
  `x' = τ(y',w)` and `w' = τ(y',u')` are determined too.
- *`u'` is off `ℓ`.* If `u' ∈ ℓ`, then `ℓ = wu' = λ(y')`, so `y' = u`, which is excluded.
- *Surjectivity.* Given a point `p ∉ ℓ`, we have `p ≠ w`. Let `y'` be the point with
  `λ(y') = wp`, so `y' ≠ u`. Set `x' = τ(y',w)`, `u' = p` and `w' = τ(y',p)`. Then:
  - `(x',y',w) ∈ T`;
  - `x' ≠ y`;
  - `(y',u',w') ∈ T`;
  - `u' ≠ w`;
  - the edge conditions `w_a = z_b` and `y_a ≠ x_b` hold.

*F2 (colour 2).* A colour-2 edge `a → c` means `c = (u,y'',z'',u'',w'')` with:

- `(u,y'',z'') ∈ T` and `y'' ≠ w`;
- `(y'',u'',w'') ∈ T` and `u'' ≠ z''`.

So `I(u,y'')`, `z'' = τ(u,y'')`, `I(w'',y'')` and `u'' = τ(w'',y'')`.

- *`λ(w'') ≠ ℓ`.* We have `w'' = u` iff `(y'',u'',u) ∈ T` iff `(u,y'',u'') ∈ T` iff
  `u'' = z''`, which is excluded. So `λ(w'') ≠ ℓ`.
- *Injectivity.* Both lines contain `y''`, so `λ(w'') ∩ ℓ = {y''}`. Hence `y''` is
  determined by `w''`, and so are `u'' = τ(w'',y'')` and `z''`.
- *`w` is off `λ(w'')`.* If `w ∈ λ(w'')`, then `w ∈ λ(w'') ∩ ℓ = {y''}`. That contradicts
  `y'' ≠ w`.
- *Surjectivity.* Given `p` with `w ∉ λ(p)`, we have `λ(p) ≠ ℓ`. Let `y''` be the point
  `λ(p) ∩ ℓ`, so `y'' ≠ w`. Set `u'' = τ(p,y'')`, `w'' = p` and `z'' = τ(u,y'')`. Then:
  - `(y'',u'',p) ∈ T`;
  - `u'' ≠ z''`, since `p ≠ u`;
  - the edge conditions `u_a = x_c` and `w_a ≠ y_c` hold.

*F3 (compatibility).* Given `b` and `c` as above, a tile `d = (X,Y,Z,U,W)` has
`b -2-> d` and `c -1-> d` iff:

- `X = u'` and `Y ≠ w'`;
- `Z = w''` and `u' ≠ y''`;
- `(u',Y,w'') ∈ T`, `(Y,U,W) ∈ T` and `U ≠ w''`.

Now `(u',Y,w'') ∈ T` iff `(w'',u',Y) ∈ T` iff `I(w'',u')` and `Y = τ(w'',u')`. Once `Y`
is fixed, `U` can be any of the `q ≥ 2` points of `λ(Y)` other than `w''`, with
`W = τ(Y,U)`. For the condition on `Y`:

- `Y = w'` means `(u',w',w'') ∈ T`.
- By (A2) applied to `(y',u',w')`, `(u',w',y') ∈ T`. So by (A3), `Y = w'` iff `w'' = y'`.

So such a `d` exists iff `I(w'',u')`, `u' ≠ y''` and `w'' ≠ y'`. The last two conditions
are automatic:

- `u' ∉ ℓ` and `y'' ∈ ℓ`, so `u' ≠ y''`;
- `w ∈ λ(y')` but `w ∉ λ(w'')`, so `y' ≠ w''`.

Such a `d` gives the paths `a→b→d` (colours 1, 2) and `a→c→d` (colours 2, 1). By (H1),
`c` is the unique filling of `a→b→d`, so there is a square with first edges `(a,b)` and
`(a,c)`. Conversely, a square gives `d`. Hence `b` and `c` are compatible iff
`u' ∈ λ(w'')`.

*F4 (connectivity).* Take points `p ≠ p'` off `ℓ`.

- If the line `pp'` does not pass through `w`, it is a vertex of `B_1(a)` adjacent to both.
- Otherwise `pp' = pw`. The line `pw` has `q` affine points and there are `q^2 > q`, so
  pick an affine `r ∉ pw`. The line `pr` differs from `pw`, so it misses `w`. The line
  `rp'` differs from `p'w = pw`, so it misses `w` too. This gives the path
  `p – pr – r – rp' – p'`.
- Every line `m ≠ ℓ` not through `w` meets `ℓ` in one point, so it has `q ≥ 2` affine
  points and hence a neighbour.

So `B_1(a)` is connected. Regularity: an affine point lies on `q + 1` lines, and exactly
one of them passes through `w`; an allowed line carries `q` affine points. ∎

**Check.** `experiments/nv-kazhdan-independence-2026-09-17/corners_all.py` (log
`corners_all.log`) confirms Proposition F at every vertex of `T0..T4` (`q = 2`) and of the
two `PG(2,3)` presentations:

- every `B_1(a)` is connected;
- the degrees are `q` on both sides;
- two vertices on one side have at most one common neighbour.

## Part G. Corollary

**Corollary G.** Let `T` be a triangle presentation over `PG(2,q)` satisfying (A1)–(A3),
whose tile 2-graph `Λ_T` satisfies (H1), (R1), (R2) and (R3). Then `Λ_T` has no brick
coding in any dimension, so Theorem A of the earlier artifact yields no embedding
`[[Λ_T]] ↪ mV`.

**Proof.** Every vertex emits `q^2 ≥ 4` edges of each colour (Proposition F), and (C1)
holds (Proposition F). Apply Theorem E. ∎

**Application to `PG(2,2)`.** For `T0..T4`, the file `certificate.log` (T0, T1) and
`certificate_uniform.log` (T0..T4), in `experiments/nv-brick-coding-2026-09-17/`, record
for T0: "row sums 4; primitive exponents 5,5; dim H^1 = 2; one transport class per
colour". The same line appears for T1..T4, except that T2 reads "primitive exponents 4,4". `rs2graph.build` asserts (H1), and `tp.py` checks (A1)–(A3). So Corollary G
reproves `cmsz-pg22-rs-two-graphs-admit-no-brick-coding` with no SAT solver. The trust
base is exact modular rank computations and union–find.

## Part H. Computations, belief update, survivors

**Computations** (`experiments/nv-kazhdan-independence-2026-09-17/`):

- `corners.py`: only a `1/q` fraction of corner pairs are compatible. So the naive
  statement "every corner pair completes" is false, and connectivity is the right
  invariant.
- `completions.py`: at vertex 0, every compatible `(k,0)/(0,k)` pair has exactly `q^k`
  completing rectangles, and a `1/q^k` fraction of pairs is compatible. Checked for
  `q = 2`, `k ≤ 3` and `q = 3`, `k ≤ 2`.
- `compat_graph.py`: the level-`k` corner graphs `B_k(a)` (`k ≤ 2`, `a ∈ {0,1}`, first two
  presentations) are connected and not unions of bicliques.
- `corners_all.py`: (C1) at every vertex (see Part F).

**Belief update.**

- Before: brick codings of Ã₂ tile 2-graphs were excluded for `q = 2` only by SAT runs
  with no DRAT logs, and for `q = 2^r ≥ 4` not at all. The rigidity proposition leaves
  dimensions `m ≤ 2r` open there.
- After: for every `q`, the class of (level-1) brick codings of triangle-presentation
  tile 2-graphs is dead as soon as the linear-algebra hypotheses (R1)–(R3) hold. The
  combinatorial part (C1) is a theorem for all `q`.
- The obstruction is local (one vertex, one coordinate). It is independent of the
  exotic/Bruhat–Tits distinction.

**Survivors on the negation route** of `some-brin-thompson-group-has-an-infinite-kazhdan-subgroup`:

1. *Triangle presentations violating (R2) or (R3).* No instance is known. (R2) and (R3)
   have not been proved in general; they are only computed for `q = 2, 3`.
2. *Block recodings.* These are brick codings of the `k`-block 2-graph `Λ^{[k]}`, whose
   level-1 corner graph is `B_k(a)`. `B_k(a)` is connected in the computed cases, but
   (R2) and (R3) for `Λ^{[k]}` are not computed, and (C1) for `Λ^{[k]}` is not proved.
3. *Codings that are not cylinder-to-brick.* This covers groupoid-level spatial
   embeddings that do not send cylinders to bricks, and non-spatial embeddings.
4. *Kazhdan groups that are not Ã₂ lattices*, for example `SL_3(Z)` or lattices in
   higher-rank buildings of other types. These have no tile 2-graph of this form.
