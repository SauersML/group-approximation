# Baumslag–Solitar groups have contractible Rips complexes: staircase triangulations

Artifact for `baumslag-solitar-groups-have-contractible-rips-complexes-proof`
(swarm run 2026-09-16). Computational check:
`experiments/baumslag-solitar-contractible-rips-2026-09-16/check_bs_rips.py`.

## Theorem

Let `m, n` be nonzero integers and `G = BS(m,n) = <a, t | t a^m t^-1 = a^n>`.
Since `a -> a^-1` induces `BS(m,n) ≅ BS(-m,-n)`, assume `m >= 1`. Put
`N = |n|` and `δ = sign(n) ∈ {±1}`, so `n = δN`.

Let `P` be a monotone lattice path from `(0,0)` to `(m,N)`: a sequence of
`m+N+1` points of `Z^2`, each obtained from the previous one by adding
`(1,0)` (a horizontal step) or `(0,1)` (a vertical step). For `(r,i) ∈ Z^2` put

`s(r,i) = a^(-δ i) t a^r ∈ G`,  `T = s(P)`,  `S = {a, a^-1} ∪ T ∪ T^-1`.

Then `S` is a finite symmetric generating set of `G` with `|S| = 2+2(m+N)`,
and the clique complex `Flag(Cay(G,S)) = R_1(G, d_S)` is a 2-dimensional
contractible simplicial complex: a triangulation of the universal cover of the
presentation complex of `<a, t | t a^m t^-1 a^-n>`.

Examples. `BS(1,1) = Z^2` with `P = (0,0),(1,0),(1,1)` gives `S = {a^±1, t^±1, (ta)^±1}`,
the triangular lattice. `BS(1,2)` with `P = (0,0),(0,1),(0,2),(1,2)` gives
`S = {a^±1, t^±1, (a^-1 t)^±1, (a^-2 t)^±1}`.

## 1. Facts about G

`G` is the HNN extension of `A = <a> ≅ Z` along the isomorphism
`<a^m> -> <a^n>`, `a^m -> a^n`. We use two standard facts about HNN
extensions: the base group embeds, and Britton's lemma (e.g. Lyndon–Schupp,
*Combinatorial Group Theory*, Springer 1977, Ch. IV §2; the section number was
not re-checked for this run).

- **(F1)** `a` has infinite order. The map `φ : G -> Z` with `φ(a) = 0`,
  `φ(t) = 1` is a well-defined homomorphism, since the relator has
  `t`-exponent sum `0`.
- **(F2)** For `k ∈ Z`: `t a^k t^-1 ∈ <a>` iff `m | k`, and then
  `t a^k t^-1 = a^(nk/m)`. If `m ∤ k`, the word `t a^k t^-1` contains no
  pinch, since `a^k ∉ <a^m>`. By Britton's lemma it is not equal to any word
  without `t`. If `k = mc`, then `t a^k t^-1 = (t a^m t^-1)^c = a^(nc)`.
- **(F3)** For `(r,i), (r',i') ∈ Z^2`: `s(r,i) = s(r',i')` iff
  `(r-r', i-i') ∈ Z(m,N)`. Indeed `s(r,i) = s(r',i')` iff
  `t a^(r-r') t^-1 = a^(δ(i-i'))`. By (F2) and (F1) this holds iff
  `r - r' = mc` and `δ(i-i') = nc = δNc` for some `c ∈ Z`.
- **(F4)** As words, `s(r,i) a = s(r+1,i)` and `a^-1 s(r,i) = s(r,i+δ)`,
  because `a^-1 a^(-δi) = a^(-δ(i+δ))`.

**The periodic path.** Let `P^ = P + Z(m,N)`. Since `P` ends at
`(0,0) + (m,N)`, the translates of `P` concatenate to a bi-infinite monotone
lattice path. Along it the coordinate sum `r+i` increases by exactly `1` per
step. So `P^` has exactly one point on each antidiagonal `r+i = const`, and
two points of `P^` that differ by `(1,0)` or `(0,1)` are consecutive on `P^`.
Every step of `P^` is a translate of a step of `P`. Also
`P^ ∩ [0,m]×[0,N] = P`, since `P ± (m,N)` meets the box only in `(m,N)`,
respectively `(0,0)`, and the other translates miss it.

- **(F5)** `T = s(P^)`, and for `p ∈ Z^2`: `s(p) ∈ T` iff `p ∈ P^`. This is
  (F3) together with the translation invariance of `P^`.
- **(F6)** `|T| = m + N`. The only coincidence among the values `s(p)`,
  `p ∈ P`, is `s(0,0) = s(m,N) = t`. By (F3) a coincidence between points of
  the box needs `c ∈ {-1,0,1}`, and `c = ±1` forces `{p,p'} = {(0,0),(m,N)}`.
  Also `s(m,N) = a^-n t a^m = a^-n a^n t = t`.

## 2. The triangulated universal cover Y

Let `X` be the presentation complex of `<a,t | w>`, `w = t a^m t^-1 a^-n`, and
let `X~` be its universal cover.

**Cells of X~.**
- Vertices: `G`.
- Edges: `(g,a)` from `g` to `ga`, and `(g,t)` from `g` to `gt`, for `g ∈ G`.
- 2-cells: one `D_g` for each `g ∈ G`. Its boundary reads `w` from `g`. The
  lifts of the single 2-cell of `X` form a `G`-torsor.

**X~ is contractible.** This is the standard fact that the presentation
complex is aspherical; here is a direct argument.
- `X~` is simply connected and 2-dimensional, so `H_2(X~;Z) = ker ∂_2`.
- Reading `w` from `g`, the boundary of `D_g` crosses `(g,t)` forwards and
  crosses `(g a^n, t)` backwards; note `g t a^m t^-1 = g a^n`. It crosses no
  other `t`-edge. So in `∂_2 D_g` the `t`-edges contribute
  `(g,t) - (g a^n, t)`.
- For a finite 2-chain `c = Σ c_g D_g`, the coefficient of `(x,t)` in `∂_2 c`
  is `c_x - c_(x a^-n)`. If `∂_2 c = 0`, then `c` is constant on each coset
  `x<a^n>`.
- These cosets are infinite by (F1) and `c` has finite support, so `c = 0`.
  Hence `H_2(X~) = 0`.
- `X~` is a simply connected CW complex with vanishing reduced homology, so it
  is contractible by the Hurewicz and Whitehead theorems (e.g. Hatcher,
  *Algebraic Topology*, Cor. 4.33; the numbering was not re-checked).

Reading `w` from `g`, the boundary vertices of `D_g` are
- top: `u_r = g t a^r` for `0 <= r <= m`;
- bottom: `b_i = g a^(δi)` for `0 <= i <= N`.

The boundary consists of the `a`-edges `u_r u_(r+1)` and `b_i b_(i+1)`, and
the `t`-edges `b_0 u_0` and `b_N u_m`; note `g a^n t = g t a^m`. These
`m+N+2` vertices are distinct. `φ` separates top from bottom, and (F1)
separates vertices within each row. So `D_g` is a polygon whose boundary
vertices are pairwise distinct.

**Staircase subdivision.** For each `(r,i) ∈ P`, draw the chord `b_i u_r`
inside `D_g`. For the two endpoints of `P` these chords are the `t`-edges
already on the boundary. The chords are non-crossing, because `P` is
monotone. Consecutive chords cut `D_g` into `m+N` triangles:
- a horizontal step `(r,i) -> (r+1,i)` gives the triangle `{b_i, u_r, u_(r+1)}`;
- a vertical step `(r,i) -> (r,i+1)` gives the triangle `{b_i, b_(i+1), u_r}`.

Let `Y` be the 2-dimensional CW complex obtained from `X~` by subdividing
every `D_g` this way. It has the same underlying space, so `Y` is
contractible.

The chord `b_i u_r` of `D_g` joins `g a^(δi)` to `g a^(δi) s(r,i)`, since
`b_i^-1 u_r = a^(-δi) t a^r = s(r,i)`. With (F6) this gives the following.

**Lemma A (labels).** `1 ∉ S`, the elements `a, a^-1`, the `m+N` elements of
`T`, and their inverses are pairwise distinct, so `|S| = 2 + 2(m+N)`. `S`
generates `G`, since `a ∈ S` and `t ∈ T`.

*Proof.* `φ = 0` on `a^±1`, `φ = 1` on `T` and `φ = -1` on `T^-1`. Also
`a ≠ a^-1`, `a ≠ 1` by (F1), and (F6) counts `T`. ∎

**Lemma B (1-skeleton).** Each edge of `Y` has two distinct endpoints, and the
map `edge -> {endpoints}` is a bijection from the edges of `Y` onto the edges
`{x, xs}`, `s ∈ S`, of `Cay(G,S)`.

*Proof.*
- *Into `Cay(G,S)`.* Each edge of `Y` has label in `S`: `a`, `t`, or
  `s(r,i)`. Its endpoints are distinct since `1 ∉ S`.
- *Onto.* Take `{x, xs}` with `s ∈ S`. If `s = a^±1`, it is an `a`-edge of
  `X~`. Otherwise swap the endpoints if needed so that `s ∈ T`, and write
  `s = s(r,i)` with `(r,i) ∈ P`. If `(r,i)` is an endpoint of `P`, then
  `s = t` and the pair is a `t`-edge. If not, it is the chord at `(r,i)` in
  `D_g` with `g = x a^(-δi)`.
- *Injective.* Let `e, e'` be edges with the same endpoints `{x, y}`.
  - If `φ(x) = φ(y)`, both are `a`-edges. Then `e = e'`, because
    `{g, ga} = {h, ha}` forces `g = h` (else `a^2 = 1`).
  - Otherwise let `x` be the endpoint with the smaller `φ`. Both `e` and `e'`
    have label `x^-1 y ∈ T`. By (F6) this label determines the path point
    `(r,i)`, up to swapping `(0,0)` and `(m,N)`.
  - If that point is an endpoint of `P`, both are the unique `t`-edge from
    `x` to `xt`. If it is interior, both are the chord at `(r,i)` in
    `D_(x a^(-δi))`. So `e = e'`. ∎

## 3. Triangles are exactly the 3-cliques

By Lemma B, every triangle of `Y` is attached homeomorphically along a
3-cycle of `Cay(G,S)` with three distinct vertices. Its vertex set is
therefore a 3-clique.

**Lemma C.** Every 3-clique of `Cay(G,S)` is the vertex set of some triangle
of `Y`.

*Proof.* Let `{x,y,z}` be a 3-clique. The increments of `φ` along
`x -> y -> z -> x` lie in `{-1,0,1}`, since `φ(S) = {-1,0,1}`, and they sum
to `0`.

- **Exactly one `a`-edge.** If all three increments were `0`, all three edges
  would be labelled `a^±1`. The vertices would then be three points of the
  coset `x<a>`, pairwise at distance `1` in `Z`; this uses (F1), and three
  such points do not exist. So exactly one increment is `0`, and the other two
  are `+1` and `-1`. Hence the clique has exactly one `a`-edge `{g, ga}`, and
  its third vertex `k` has `φ(k) - φ(g) = ε ∈ {±1}`.
- **Case `ε = -1`.** Then `u := k^-1 g ∈ T` and `k^-1 (ga) = ua ∈ T`.
  - Write `u = s(p)` with `p ∈ P`. By (F4), `ua = s(p + (1,0))`, so (F5)
    gives `p + (1,0) ∈ P^`.
  - So `p` and `p+(1,0)` are consecutive on `P^`, joined by a horizontal step.
    Translating by a multiple of `(m,N)` changes no value of `s` by (F3), so
    we may assume this is a step `(ρ,ι) -> (ρ+1,ι)` of `P` with
    `u = s(ρ,ι)`.
  - Put `g_0 = k a^(-δι)`. In `D_(g_0)`: `b_ι = k`,
    `u_ρ = k s(ρ,ι) = k u = g`, and `u_(ρ+1) = g a`. So `{g, ga, k}` is the
    vertex set of the triangle of `D_(g_0)` for this step.
- **Case `ε = +1`.** Then `u := g^-1 k ∈ T` and `(ga)^-1 k = a^-1 u ∈ T`.
  - Write `u = s(p)` with `p ∈ P`. By (F4), `a^-1 u = s(p + (0,δ))`, so
    `p + (0,δ) ∈ P^` by (F5).
  - So `p` and `p + (0,δ)` are consecutive on `P^`, joined by a vertical
    step. After a translation, this is a step `(ρ,j) -> (ρ,j+1)` of `P`,
    where `p = (ρ,j)` if `δ = 1` and `p = (ρ,j+1)` if `δ = -1`.
  - Put `p = (ρ,i)` and `g_0 = g a^(-δi)`. In `D_(g_0)`: `b_i = g`,
    `b_(i+δ) = g a^(δ·δ) = g a`, and `u_ρ = g a^(-δi) t a^ρ = g s(ρ,i) = g u = k`.
    The indices `i` and `i+δ` are `j` and `j+1` in some order. So `{g, ga, k}`
    is the vertex set of the triangle of `D_(g_0)` for this vertical step. ∎

## 4. No duplicate triangles, no 4-cliques

Consider the cellular chain complex of `Y` with `F_2` coefficients. `Y` is
2-dimensional and contractible, so `H_2(Y;F_2) = ker(∂_2) = 0`. For a triangle
`τ`, `∂_2 τ` is the sum of its three edges. By Lemma B, these three edges are
determined by the vertex set of `τ`.

**Lemma D.** Distinct triangles of `Y` have distinct vertex sets.

*Proof.* Two distinct triangles with the same vertex set have the same
boundary. Their sum is then a nonzero 2-cycle. ∎

**Lemma E.** `Cay(G,S)` has no 4-clique.

*Proof.* Let `{w,x,y,z}` be a 4-clique. By Lemmas C and D, each of its four
3-subsets is the vertex set of a unique triangle of `Y`. Each edge of the
clique lies in exactly two of these triangles. So the sum of the four
triangles is a nonzero 2-cycle. ∎

## 5. Conclusion

By Lemmas B and D, `Y` is a 2-dimensional regular CW complex in which every
closed cell is a simplex determined by its vertex set. Hence `Y` is (the
realization of) a simplicial complex. Moreover:
- its 1-skeleton is `Cay(G,S)` (Lemma B);
- its triangles are exactly the 3-cliques (Lemmas C and D);
- there are no 4-cliques (Lemma E), so `Flag(Cay(G,S))` has no simplices of
  dimension `>= 3`.

So `Flag(Cay(G,S)) = Y`, which is contractible. `S` is a finite symmetric
generating set of `G` not containing `1` (Lemma A). Item 1 of
`group-rips-complexes-are-cayley-graph-flag-complexes` gives
`Flag(Cay(G,S)) = R_1(G,S)`, the Rips complex of `(G, d_S)` at scale `1`. ∎

**Remarks.**
1. `χ` check. `G` acts freely on `Y` with `1` vertex orbit, `m+N+1` edge
   orbits (`a`, `t`, `m+N-1` interior chords) and `m+N` triangle orbits. So
   `χ(Y/G) = 1 - (m+N+1) + (m+N) = 0 = χ(X)`.
2. Not used in the proof. Lemma C shows that exactly `m` triangles lie below
   an `a`-edge and exactly `N` lie above it. So for `m+N >= 3`, `Y` is not a
   surface along its `a`-edges.
3. The computation `check_bs_rips.py` verifies Lemmas A, C and E, and the
   triangle-to-clique match, by brute force in the HNN normal form. It covers
   all `1 <= m <= 4`, `1 <= |n| <= 4` and every staircase path: 484
   generating sets. It also cross-checks the normal form against the faithful
   affine representation of `BS(1,n)` for `n ∈ {2,3,-2,-3}`. (An earlier
   version of this remark also claimed a mutation test; no such test is in
   that script. The referee's independent script `referee_check_bs.py`, in
   the same directory, does include one.)
4. Referee cross-check (2026-09-16), not used in the proof.
   `referee_check_bs.py` uses its own Britton normal form. For up to 40
   random staircase paths in each of `BS(2,3)`, `BS(3,-5)`, `BS(5,2)`,
   `BS(6,4)`, `BS(1,7)`, `BS(5,-7)`, `BS(4,6)`, `BS(7,7)`, `BS(6,-9)`,
   `BS(2,-2)`, `BS(3,1)` and `BS(8,5)` (329 generating sets), it checks
   three things at the vertex `1`:
   - `|S| = 2+2(m+N)`;
   - there are exactly `3(m+N)` 3-cliques containing `1`;
   - there is no 4-clique.

   Two non-staircase point sets are rejected. Output: `referee_output.txt`.
