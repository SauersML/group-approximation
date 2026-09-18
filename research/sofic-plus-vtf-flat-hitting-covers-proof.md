---
rg: 2
id: sofic-plus-vtf-flat-hitting-covers-proof
kind: route
title: Sofic monodromy cover, random flat-hitting vertex set, girth-raising orbihedron over it, then a torsion-free finite-index subgroup
target: sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers
requires: []
---

Notation as in the target. `(S)` and `(V2)` are hypotheses of the theorem, not
prerequisites of this route. Lemmas 1–3 and Step 4 refer to
`sparse-branched-covers-sofic-pi1-reduction-proof`, which is established and
proved for this generality. `d` is the largest diameter of a closed cell of `Y`,
and `c_Delta` is the largest number of closed cells of `Delta` at one vertex.

**Imports.**
* Bridson–Haefliger (B–H), *Metric spaces of non-positive curvature*: I.7.19,
  II.1.4, II.4.1 and II.5.4 (as in the reduction proof); II.2.9, the flat
  triangle lemma, used only for convexity of geodesics; III.H.1.5, the flat plane
  theorem; and the Švarc–Milnor lemma I.8.19.
* Complexes of groups, B–H III.C. The statements are quoted from J. T. Verano,
  *Immersions of complexes of groups*, arXiv:2510.01516, §2, read at source on
  2026-09-18 through the HTML rendering and a summariser, so they are
  near-verbatim:
  - Def. 2.6: a complex of groups over a scwol consists of local groups `G_σ`,
    injective homomorphisms `ψ_a: G_(i(a)) -> G_(t(a))`, and twisting elements
    `g_(a,b) in G_(t(a))`.
  - Def. 2.14: "A complex of groups is developable if it arises from a group
    acting on a simply connected scwol." Its local groups "are precisely the
    stabilizers of objects up to conjugation."
  - Thm. 2.17: "If G(𝒴) is developable, the development D(𝒴,ι_T) is simply
    connected ... G(𝒴) and ι_T are the complex of groups and morphism
    associated to the action of π_1(G(𝒴),T) on D(𝒴,ι_T)." Here "associated"
    is [BH99, Definition III.𝒞.2.9(1)].
  - Def. 2.24: the local development `𝒴(γ~)` at an object `γ`.
  - Prop. 2.25: "Let G(𝒴) be a developable complex of groups over a scwol 𝒴.
    For each lift γ̄ of γ∈V(𝒴) in D(𝒴,ι_T), there exists a Stab(γ̄)-equivariant
    embedding given by st(γ~)⟶|D(𝒴,ι_T)|".
  - Def. 2.29: "A complex of groups G(𝒴) is non-positively curved if for all
    σ∈V(𝒴), st(σ~) is non-positively curved."
  - Thm. 2.30 [BH99, Theorem III.𝒞.4.17]: "A non-positively curved complex of
    groups is developable."
* Free groups are residually finite.

A **sofic model** of `G` for a finite set `F ∋ 1` and `ε > 0` is a map
`Σ: F -> Sym(n)` with two properties:
* for `g, h, gh in F`, `Σ(g)Σ(h)i = Σ(gh)i` for all but at most `εn` points `i`;
* for `g in F \ {1}`, `Σ(g)i != i` for all but at most `εn` points `i`.

## Step 1. Sofic models of G, and the covers `X_n`

**Induction.** Let `H <= G` be sofic of index `m`, and let `T ∋ 1` be a
transversal of `G/H`. For `g in G` and `t in T`, write `gt = t' h(g,t)` with
`t' in T` and `h(g,t) in H`.

Given `F`, let `E` be the set of all `h(g,t)^(±1)` for `g in F F`, together with
their pairwise products. Take an `(E, δ)` model `σ` of `H` on `[k]`, and set
`Σ(g)(i,t) = (σ(h(g,t)) i, t')` on `[k] x T`.

From `h(g_2 g_1, t) = h(g_2, t_1') h(g_1, t)`, `Σ` is multiplicative off
`δkm` points. If `Σ(g)(i,t) = (i,t)` with `g != 1`, then `t' = t` and
`h(g,t) = t^(-1) g t != 1` is fixed at `i`. So `Σ` is an `(F, δm)` model, and
`G` is sofic.

**The covers.** Run Step 4 of the reduction proof with an `(F', ε)` model `Σ`
of `G` on `[n]`, where `F'` is enlarged below. It gives an `n`-sheeted branched
cover `X = X_n -> Y` whose restriction over `Y°` has monodromy
`f_i -> Σ(k_i)`. Moreover,

```text
beta(X) <= (#words)(L + 1) ε .                                         (1.1)
```

By Step 0, `X` is locally CAT(0), `X~` is CAT(0), and `q: X~ -> X -> Y`. Write
`q_X: X~ -> X`, and `ρ(x) = d(x, B~)` for a vertex `x` of `X~`. Every vertex of
`X` has a type `y`, its image in `Y`, and `|V(X)| <= |V(Y)| n`.

## Step 2. Most far vertices develop injectively

Fix `ρ >= 4d` and put `r = ρ + 1`. For each vertex `y` of `Y`, fix three things:
* `o_y in π^(-1)(y)`, with `|g|_y = d(o_y, g o_y)`;
* the basepoint `*_y in S_y` of Step 4;
* a lift `õ_y` of `*_y` in the star of `o_y`.

Let `P_y = {g in G : 0 < |g|_y < 4r}`, which is finite. For each `g in P_y`,
choose a loop `c_(y,g)` in `Y°` at `*_y` whose lift to `Delta` from `õ_y` ends
at `g õ_y`. It exists because `pi_1(Y°) -> G` is onto (Step 4).

Let `ℓ` bound the lengths of all `c_(y,g)`, and set `R_0 = 4r + ℓ + d + 2`. A
vertex `x` of `X` is **far** if `d_X(x, B) >= R_0`.

For a far `x` of type `y` with lift `x~`, set

```text
ι_x = q_X o dev_(x~, o_y)^(-1) :  B_Delta(o_y, R_0) -> X .
```

By Lemma 2.1 this does not depend on the choice of `x~`. Call `x` **tame** if it
is far and `ι_x` is injective on `B_Delta(o_y, r)`. `*` is the partial action of
Lemma 4, for the vertex `o_y`.

**Lemma 5.** Let `x~` be far of type `y`, and suppose `ι_x` is not injective on
`B_Delta(o_y, r)`. Then there are `g in P_y` and `λ in Lambda \ {1}` with
`g^(-1) * x~ = λ x~`.

*Proof.* Write `o = o_y` and `dev = dev_(x~, o)`. Take `a != b` in
`B_Delta(o, r)` with `ι_x a = ι_x b`, and put `p = dev^(-1) a` and
`p' = dev^(-1) b`. These are distinct and have the same image in `X`, so
`p' = λ p` with `λ != 1`. Also `π a = π b`, so `b = g a` with `g in G`, and
`g != 1` because `a != b`. Then

```text
|g| <= d(o,a) + d(a,b) + d(b, g o) = 2 d(o,a) + d(a,b) < 4r ,
```

so `g in P_y`.

Next, `dev_(λx~, o) = dev o λ^(-1)` by Lemma 2.1, so `dev_(λx~, o)(p') = a`.
By Lemma 2.2, `g o dev_(λx~, o) = dev_(λx~, g o)`. This map and `dev` are both
lifts of `q` through `π`. They are defined on
`U = B(x~, ρ(x~)) ∩ B(λx~, ρ(x~))`, which is convex, hence connected. They
agree at `p' in U`, since both send it to `b`. So they agree on `U`.

Now `d(x~, λx~) <= d(x~, p') + d(p, x~) < 2r < ρ(x~)`, so `λx~ in U`. Therefore
`dev(λx~) = g o`, which says exactly `g^(-1) * x~ = λ x~`. QED

**Lemma 6 (monodromy of a far vertex).** For an unbranched `x` of type `y`, let
`i_x` be the unique point over `*_y` on the small link sphere of `x`. Then
`x -> i_x` is injective on unbranched vertices of type `y`.

Suppose moreover `x` is far and `h in P_y`. Then the lift to `X` of `c_(y,h)`
from `i_x` ends at `i_(x')`, where `x' = q_X(h^(-1) * x~)`.

*Proof.* Injectivity holds because distinct vertices have disjoint small
spheres. For the second statement, let `x~_* = dev^(-1)(õ_y)`, which lies in the
star of `x~` and over `i_x`.

`dev` is an isometric bijection `B(x~, ρ(x~)) -> B(o, ρ(x~))` with
`π o dev = q`. So the `q`-lift of `c_(y,h)` from `x~_*` is `dev^(-1)` of its
`π`-lift from `õ_y`. That lift stays in `B(o, ℓ + d)` and ends at `h õ_y`.

Let `x~' = dev^(-1)(h o) = h^(-1) * x~`. By Lemmas 2.3 and 2.2,
`dev_(x~', o) = h^(-1) o dev` near `x~'`. So `dev^(-1)(h õ_y)` is the point
`x~'_*` of the star of `x~'`, and its image in `X` is `i_(x')`. Finally
`ρ(x~') >= ρ(x~) - |h| > 0`, so `x'` is unbranched. QED

**Counting.** Transport the fibre over `*_y` to `[n]` along `γ_y`. Then the
monodromy of `c_(y,g)` becomes the product of the `Σ(k_i)^(±1)` along a word
`w_(y,g)`. Its image `ḡ` in `G` is nontrivial, because `c_(y,g)` is nontrivial in
`pi_1(Y, *_y)`.

Enlarge `F'` by the images of all subwords of all `w_(y,g)`, and let
`W = max |w_(y,g)|`. There are two estimates.
* `Σ(k)^(-1)` and `Σ(k^(-1))` agree off `2εn` points. Chaining along the word,
  as in Step 4, the product along `w_(y,g)` agrees with `Σ(ḡ)` off `3Wεn`
  points.
* `Σ(ḡ)` moves all but `εn` points.

Let `x` be far, unbranched and not tame. Take `g, λ` from Lemma 5. By Lemma 6
with `h = g`, `x' = q_X(λx~) = x`, so the monodromy of `c_(y,g)` fixes `i_x`.
Hence `i_x` lies in one of the exceptional sets above. By injectivity of
`x -> i_x`,

```text
#{far, not tame} <= |V(Y)| · (Σ_y |P_y|) · (3W + 1) · ε n .              (2.1)
```

(A far vertex is unbranched, since `d(x,B) > 0`.) By Lemma 3,

```text
#{not far} <= (c_Y v_Delta(R_0) + 1) β(X) n .                            (2.2)
```

For fixed `ρ`, both bounds are `o(n)` as `ε -> 0`, by (1.1).

## Step 3. Flat disks are few and fat

A **flat `R`-disk centred at `o`**, in a CAT(0) piecewise Euclidean 2-complex
`Z`, is the image `F = φ(D_R)` of an isometric embedding `φ` of the closed
Euclidean disk with `φ(0) = o`.

**Lemma 7.** Let `z in F` with `d(o,z) < R - d`. Then `z` lies in a closed
2-cell `C ⊂ F`.

*Proof.* Let `F° = φ(open disk)`, a 2-manifold. A locally finite graph contains
no open subset of a 2-manifold, so points of `F°` in open 2-cells accumulate at
`z`. By local finiteness, infinitely many of them lie in one open cell `int C`
with `z in C`.

Since `diam C <= d`, we have `C ⊂ B(o, R)`. Points of `F` at distance `< R` from
`o` lie in `F°`, so `F ∩ int C = F° ∩ int C`. This set is closed in `int C`. It
is also open in `int C`, by invariance of domain. It is nonempty and `int C` is
connected, so `C ⊂ F`. QED

**Lemma 8 (few).** Let `A(ρ)` be the largest number, over vertices `o` of
`Delta`, of distinct sets `F ∩ B̄(o, ρ)`, where `F` runs over flat `3ρ`-disks
centred at `o`. Then `log A(ρ) <= κ(ρ + 1)` for a constant `κ = κ(Y)`.

*Proof.* Put `s = 3ρ - 2d`. Choose `a, b, c in F` whose `φ`-preimages are the
vertices of an equilateral triangle with circumcentre 0 and circumradius `s`.
By Lemma 7 they lie in closed cells `C_a, C_b, C_c ⊂ F`. Let `a*, b*, c*` be
the barycentres of these cells.

Let `F'` be any flat `3ρ`-disk centred at `o` that contains
`C_a ∪ C_b ∪ C_c`. Let `T` be the union of the geodesics `[a*, z]` for
`z in [b*, c*]`. Geodesics in `Delta` are unique and `F, F'` are convex, so
`T ⊂ F ∩ F'`.

In the coordinates of `F`, `T` is a Euclidean triangle whose vertices are
within `d` of those of the equilateral triangle. Each side is therefore at
distance at least `s/2 - d > 0` from `0`, and this stays positive along the
straight-line homotopy from the equilateral triangle. So `0 in T`, and

```text
B̄(o, ρ) ∩ F ⊂ T      since   s/2 - d = 3ρ/2 - 2d >= ρ   for ρ >= 4d .
```

The four points `o, a*, b*, c*` have the same pairwise distances in `F'`, so
the same holds in `F'`. Hence

```text
F ∩ B̄(o, ρ) = T ∩ B̄(o, ρ) = F' ∩ B̄(o, ρ) .
```

The set is therefore determined by the triple of cells, each of which meets
`B(o, 3ρ)`. By Švarc–Milnor (B–H I.8.19), the number of cells meeting
`B(o, R)` grows at most exponentially in `R`, uniformly in `o`. QED

**Lemma 9 (fat).** Every `F ∩ B̄(o, ρ)` contains at least `c_1 ρ^2` vertices,
where `c_1 = 27π / (16 a_max c_Delta)` and `a_max` is the largest cell area.

*Proof.* By Lemma 7, the cells `C ⊂ F` meeting `B(o, ρ - d)` cover
`F ∩ B(o, ρ - d)`, and each of them lies in `B̄(o, ρ)`. Since
`ρ - d >= 3ρ/4`, there are at least `9πρ^2 / (16 a_max)` of them. Each cell has
at least 3 vertices, and each vertex lies in at most `c_Delta` cells. QED

## Step 4. A random flat-hitting set

Let `S_0 = V(X) \ {tame}`. It contains `B`. For a tame `x` of type `y`, let

```text
𝒜_x = { ι_x( V(Delta) ∩ F ∩ B̄(o_y, ρ) ) :  F a flat 3ρ-disk centred at o_y } .
```

Since `ι_x` is injective on `B(o_y, r)` and maps vertices to vertices,
`|𝒜_x| <= A(ρ)` and every member has at least `c_1 ρ^2` elements, by Lemmas 8
and 9.

Put each tame vertex into `S_rand` independently, with probability
`π_ρ = (log A(ρ) + ρ) / (c_1 ρ^2)`. Take `ρ` large, so that `π_ρ < 1`. A member
of `𝒜_x` meeting `S_0` is hit. Any other member consists of tame vertices, so
it misses `S_rand` with probability at most

```text
(1 - π_ρ)^(c_1 ρ^2) <= e^(-ρ) / A(ρ) .
```

Let `S_fix` be the set of tame `x` for which some member of `𝒜_x` misses
`S_0 ∪ S_rand`. Then `P(x in S_fix) <= e^(-ρ)`.

Fix an outcome with `|S_rand| + |S_fix|` at most its expectation, which is at
most `|V(Y)| (π_ρ + e^(-ρ)) n`. Set `S = S_0 ∪ S_rand ∪ S_fix`.

**(P).** If `x ∉ S` is of type `y` and `F` is a flat `3ρ`-disk centred at `o_y`,
then `ι_x( V ∩ F ∩ B̄(o_y, ρ) )` meets `S`.

**Size.** By (2.1) and (2.2),

```text
|S \ B| / n <= |V(Y)| (π_ρ + e^(-ρ)) + o_(ε -> 0)(1)      (ρ fixed).      (4.1)
```

**Lemma 10.** There is no locally isometric map `f: D̄_(3ρ) -> X \ S` with
`f(0)` a vertex.

*Proof.* Let `x = f(0)`. Since `x ∉ S`, `x` is tame. Lift `f` to
`f~: D̄ -> X~` with `f~(0) = x~`. Segments map to local geodesics, which are
geodesics (B–H II.1.4). So `f~` is an isometric embedding into
`B̄(x~, 3ρ) ⊂ B(x~, R_0)`.

Hence `F = dev_(x~, o_y)(f~(D̄))` is a flat `3ρ`-disk centred at `o_y`, and
`f = ι_x o dev o f~`. So `f(D̄)` contains `ι_x(V ∩ F ∩ B̄(o_y, ρ))`, which meets
`S` by (P). This is a contradiction. QED

**One component.** Let `X^(j)` be the components of `X`, with `n_j` sheets. The
average of `(Σ_(x in S ∩ X^(j)) d_x) / n_j`, weighted by `n_j / n`, is
`(Σ_(x in S) d_x) / n`. So some component satisfies

```text
(Σ_(x in S ∩ X^(j)) d_x) / n_j  <=  β(X) + |S \ B| / n .                   (4.2)
```

Replace `X` by that component and `S` by `S ∩ X^(j)`. Lemma 10 is unaffected,
since it is local.

## Step 5. A girth-raising orbihedron over (X, S)

**Link covers.** For `x in S` of type `y`, the link `L_x = Lk_X(x)` is a finite
connected graph covering `Lk_Y(y)`, so it contains a cycle. Its fundamental
group is free and nontrivial.

The closed non-backtracking paths of length `< g_y` in `L_x`, conjugated to a
base vertex, give finitely many nontrivial elements. By residual finiteness,
choose a proper finite-index normal subgroup `N_x` avoiding all of them. Let
`L'_x -> L_x` be the connected regular cover with group `Q_x = pi_1/N_x != 1`.

A cycle of length `m` in `L'_x` maps to a closed non-backtracking path of
`L_x`, whose based class lies in `N_x`. Hence `m >= g_y`. The angular girth of
`L'_x` is therefore greater than `2π`.

**The complex of groups.** Let `𝒳` be the scwol of the first barycentric
subdivision of `X`. Its objects are the cells, and there is an arrow
`a: τ -> σ` for each face `σ ⊊ τ`. Since `dim X = 2`, `𝒳` has composable pairs
but no composable triples. Define `G(𝒳)` as follows.
* `G_x = Q_x` for `x in S`, and `G_σ = 1` for every other object.
* Every `ψ_a` is trivial. Its domain `G_(i(a))` is the group of a cell of
  positive dimension.
* `g_(a,b) = 1` unless `t(a) = x in S`. For that case, see below.

The axioms of B–H III.C.2.1 are vacuous here. The compatibility
`Ad(g_(a,b)) ψ_(ab) = ψ_a ψ_b` holds between maps out of a trivial group, and
the cocycle condition concerns composable triples, of which there are none. So
**any** choice of `g_(a,b) in Q_x` gives a complex of groups.

**Choosing the twisting.** Fix `x in S`. The arrows `c` with `t(c) = x` are the
vertices of the barycentric subdivision `L_x^b`. They are edge-type when `i(c)`
is an edge and corner-type when `i(c)` is a 2-cell. The composable pairs
`(c,d)` with `t(c) = x` are the edges of `L_x^b`: a 2-cell `t`, an edge
`e ⊂ t`, and both containing `x`.

By Def. 2.23 as quoted, with trivial `G_(i(·))`, the upper link `Lk(x~)` is a
graph with three pieces of data:
* vertices `Q_x x {c}`;
* edges `Q_x x {(c,d)}`;
* the edge `(g,c,d)` joins `(g, c)` to `(g g_(c,d), cd)`, as the quoted
  composition rule shows.

`Q_x` acts by left multiplication, freely, with quotient `L_x^b`. This is the
derived graph of the voltage assignment `(c,d) -> g_(c,d)`.

Now choose a lift `c~` in `(L'_x)^b` of every vertex `c` of `L_x^b`. The lift of
the edge `(c,d)` that starts at `c~` ends at `h (cd)~` for a unique `h in Q_x`.
Put `g_(c,d) = h`. If the opposite orientation convention is intended, use
`h^(-1)`; both choices are allowed.

Then `(g, c) -> g c~` is a `Q_x`-equivariant isomorphism
`Lk(x~) -> (L'_x)^b`. Hence the local development at `x` is the cone on
`L'_x`, with its cells metrized as the corresponding cells of `X`.

**Non-positive curvature (Def. 2.29).**
* At `x in S`, `st(x~)` is an open subset of the Euclidean cone `C(L'_x)`. That
  cone is CAT(0), since `L'_x` has angular girth `>= 2π` (B–H II.5.4 and
  II.3.14).
* At every other object `σ`, the local group and all twisting at `σ` are
  trivial. So `st(σ~)` is isometric to the open star of `σ` in `X`, which is
  locally CAT(0) by Step 0.

By Thm. 2.30, `G(𝒳)` is developable. Let `D` be the development and
`Γ = pi_1(G(𝒳), T)`. By Thm. 2.17 and Def. 2.14:
* `D` is simply connected;
* `Γ \ D = 𝒳`;
* stabilizers are conjugates of local groups, so they are finite, and trivial
  off the lifts of `S`.

Let `x̄` lie over `x in S`. By Prop. 2.25, there is a `Stab(x̄)`-equivariant
embedding `st(x~) -> |D|` sending `x~` to `x̄` and `Lk(x~)` into `Lk_D(x̄)`.
The lifts of an arrow
`a: τ -> x` ending at `x̄` form one `Stab(x̄)`-orbit with trivial stabilizers. So
`Lk_D(x̄)` has exactly as many vertices and edges as `L'_x`, and the embedding
is onto the star. Therefore `Lk_D(x̄) = L'_x` equivariantly.

Metrize `|D|` by pulling back the cells of `X`. It is a piecewise Euclidean
2-complex with finitely many shapes. Its links are:
* at lifts of `x in S`, `L'_x`;
* elsewhere, links of `X`, since the action is free near those points.

So `D` is locally CAT(0), hence CAT(0) (II.4.1). `Γ` acts properly and
cocompactly, since stabilizers are finite and `Γ \ D = X` is compact. The map
`D \ S̄ -> X \ S` is a covering and a local isometry, where `S̄` is the
preimage of `S`.

**No flat plane.** Let `E ⊂ D` be isometric to `E^2`.

If `x̄ in E` lies over `S`, then the directions of `E` at `x̄` form a circle of
angular length `2π`, embedded in `Lk_D(x̄) = L'_x` (B–H I.7.16 for the angle
metric). That is a cycle of length `2π`, contradicting angular girth `> 2π`.
So `E ⊂ D \ S̄`.

By Lemma 7, `E` contains a closed cell, hence a vertex `ô`. The quotient
restricted to `B̄_E(ô, 3ρ)` is a locally isometric map `D̄_(3ρ) -> X \ S`
centred at a vertex, which contradicts Lemma 10.

So `D` contains no flat plane, and by B–H III.H.1.5 it is hyperbolic. By
Švarc–Milnor, `Γ` is word-hyperbolic.

## Step 6. Apply (V2)

`Γ` is hyperbolic and acts properly and cocompactly by cellular isometries on
the CAT(0) piecewise Euclidean 2-complex `D`, which has finitely many shapes.
By (V2), `Γ` has a torsion-free subgroup of finite index. Its normal core
`Λ_0` is torsion-free, normal and of finite index `M`. Finite stabilizers meet
`Λ_0` trivially, so `Λ_0` acts freely.

Let `X' = Λ_0 \ D`. It is finite and connected, and it maps
`X' -> Γ \ D = X -> Y` with every closed cell mapped isometrically.

**Links.**
* At a vertex over `x in S`, the link is `L'_x`, which is connected. Its map
  to `Lk_Y(y)` is `L'_x -> L_x -> Lk_Y(y)`, a covering of degree
  `|Q_x| d_x >= 2`.
* At any other vertex `z`, the link maps isomorphically onto `Lk_X(z)`, of
  degree `d_z = 1` over `Y`, since `B ⊂ S`.

So `X' -> Y` is a branched cover, and its branch set `B'` is exactly the
preimage of `S`. Condition **(G)** holds by Step 5.

**Mass.**
* A generic point of `Y` has `M n_j` preimages, so `X'` has `N' = M n_j`
  sheets.
* Since `Λ_0` is normal and meets `Stab(x̄)` trivially, `x in S` has
  `M / |Q_x|` preimages, each of degree `|Q_x| d_x`.

By (4.2),

```text
β(X') = M Σ_(x in S) d_x / (M n_j)  <=  β(X) + |S \ B| / n .
```

**Choice of constants.** Given `η`, first take `ρ >= 4d` so large that
`π_ρ < 1` and `|V(Y)| (π_ρ + e^(-ρ)) < η/2`. This fixes `r`, the `P_y`, `W`,
`ℓ` and `R_0`. Then take `ε` so small that (1.1), (2.1) and (2.2) give
`β(X) + (|S \ B| - |S_rand| - |S_fix|) / n < η/2`. By (4.1), `β(X') < η`.

**(H) with `R = 3ρ + d`.** Let `f: D̄_R -> X' \ B'` be locally isometric.
`X' \ B' -> X \ S` is the quotient of the free action of `Γ/Λ_0` on
`Λ_0 \ (D \ S̄)`, so it is a covering and a local isometry. Hence the composite
`f_1: D̄_R -> X \ S` is locally isometric.

Lift `f_1` to an isometric embedding into `X~`, as in Lemma 10. By Lemma 7, its
image contains a closed cell through the image of `0`, and so a vertex `v` at
distance `<= d` from it. Restricting `f_1` to the `3ρ`-disk about the preimage
of `v` gives a locally isometric map `D̄_(3ρ) -> X \ S` centred at a vertex,
which contradicts Lemma 10.

A flat `R`-disk of `Delta` lifted to `X'` from a vertex and avoiding `B'` would
be such an `f`. QED

## What is and is not used

* Soficity enters only through Step 1: the covers `X_n` and the good fibre
  points of Step 2.
* (V2) enters only in Step 6.
* No residual finiteness of `Γ` is assumed. Only virtual torsion-freeness is
  needed, so the finite residual of `Γ` may be large.
* The complexes of groups used have trivial edge and face groups, so only the
  vertex twisting matters.
