---
rg: 2
id: sparse-branched-covers-sofic-pi1-reduction-proof
kind: route
title: Develop B-free balls by covering uniqueness, then induce a model of G from a sofic model of pi_1(X)
target: sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
requires: []
---

Notation as in the target.  Standard imports: covering space theory; the
Gromov link condition and Cartan--Hadamard theorem for piecewise Euclidean
complexes with finitely many shapes (Bridson--Haefliger, *Metric spaces of
non-positive curvature*, I.7.19, II.5.4, II.4.1); and the fact that local
geodesics in a CAT(0) space are geodesics (B--H II.1.4).

## Step 0. Curvature (part 3)

A covering of graphs `L' -> L` maps every embedded cycle of `L'` to a closed
path without backtracking of the same angular length.  Such a path contains
an embedded cycle of no greater length.  Hence `girth(L') >= girth(L)`.  The
links of `X` cover links of `Y`, so they have angular girth at least `2 pi`,
and `X` is locally CAT(0) (B--H II.5.4).  `X` is a finite complex with
finitely many shapes, hence complete geodesic (I.7.19).  So `X~` is CAT(0)
(II.4.1), and `Lambda = pi_1(X)` acts on it freely and cocompactly by deck
transformations.  Write `q: X~ -> X -> Y` and `pi: Delta -> Y`.  Let `B~` be
the preimage of `B` in `X~`; it is discrete and `Lambda`-invariant.

## Step 1. Developing B-free balls

**Lemma 1.**  Let `x` be a vertex of `X~` and `r > 0` with
`B(x,r) cap B~ = empty`, and let `o in Delta` with `pi(o) = q(x)`.  There is
a unique continuous `dev = dev_(x,o): B(x,r) -> Delta` with
`pi o dev = q` and `dev(x) = o`.  It is an isometric bijection onto
`B_Delta(o,r)`.

*Proof.*  `B(x,r)` is convex in the CAT(0) space `X~`, hence contractible
and locally path connected.  `pi` is a covering, so the lift exists and is
unique.

On `X~ \ B~` the map `q` is a local isometry and a local homeomorphism.
Away from vertices this is because `p` is a covering there.  At a vertex of
degree 1, the star of `x` maps isomorphically onto the star of `p x`.  So
`dev` is a local isometry.

For `a in B(x,r)` the geodesic `[x,a]` lies in the ball and maps to a local
geodesic of `Delta`.  That is a geodesic (II.1.4), so
`d(o, dev a) = d(x,a)`.

*Surjectivity.*  Take the geodesic `c: [0,l] -> Delta` from `o` with `l < r`.
Lift `pi o c` through `q` starting at `x`, and let `[0,t)` be the maximal
lifted interval.  The lift is 1-Lipschitz, so it converges in the complete
space `X~` to a point at distance at most `t < r` from `x`.  That point is
not in `B~`, so `q` is a local homeomorphism there and the lift extends past
`t`.  Hence `t = l`.  By uniqueness of the lift `dev`, `dev` of the lifted
path is `c`.

*Injectivity.*  For `a in B(x,r)`, `dev([x,a])` is the geodesic `[o, dev a]`.
Paths through a local homeomorphism of Hausdorff spaces lift uniquely from
a given start.  So `a` is recovered from `dev a` by lifting `[o, dev a]`.

*Isometry.*  For `a,b` in the ball, `[a,b]` lies in the ball.  Its image is a
local geodesic, hence a geodesic, so `d(dev a, dev b) = d(a,b)`.  QED

**Lemma 2 (equivariance).**
1. If `lambda in Lambda`, then `dev_(lambda x, o) = dev_(x,o) o lambda^(-1)`.
2. If `g in G` (deck group of `pi`), then `dev_(x, g o) = g o dev_(x,o)`.
3. If `B(x', r') subset B(x, r)` and `o' = dev_(x,o)(x')`, then
   `dev_(x',o')` is the restriction of `dev_(x,o)`.

*Proof.*  In each case both sides are lifts of the same map from a simply
connected ball, agreeing at one point.  Use that `q o lambda = q`, that
`pi o g = pi`, and that `B~` is `Lambda`-invariant.  QED

## Step 2. Few vertices are near the branch set

Let `c_Y` be the largest number of cells of `Y` incident to one vertex, and
let `v_Delta(R)` be the largest number of vertices in a ball of radius `R`
about a vertex of `Delta`.

**Lemma 3.**  `#{vertices y of X : d_X(y,B) < R} <= (c_Y v_Delta(R) + 1) beta(X) N`.

*Proof.*  Points of `B` contribute `|B| <= beta N`.

Otherwise let `s = d(y,B) in (0,R)`.  Let `c: [0,s] -> X` be a geodesic from
some `b in B` to `y` with `c((0,s]) cap B = empty`.  Near `b` the space is
the Euclidean cone on `Lk(b)`, and geodesics from the cone point are radial.
So `c((0,u))` lies in one open cell `e` incident to `b`.  There are at most
`c_Y d_b` such cells.

`p` is a local isometry on `X \ B`.  So `p o c` lifts to a path
`c~: [0,s] -> Delta` with `c~(0) = o_(p b)`, a fixed lift of `p b`, and `c~`
is a local geodesic on `(0,s]`.  Therefore `d(c~(u), c~(s)) = s - u` for all
`u > 0`, so `c~` is the geodesic from `o_(p b)` to the vertex `c~(s)`, which
lies in `B_Delta(o_(p b), R)`.

The triple `(b, e, c~(s))` determines `y`.  It determines `c~`, hence
`p o c`.  On `(0,u)` the path `c` is the unique preimage of `p o c` in the
open cell `e`, since `p` is injective on `e`.  Lifts through the local
homeomorphism `X \ B -> Y` agreeing on an open interval agree everywhere.
Summing `c_Y d_b v_Delta(R)` over `b` gives the bound.  QED

Fix a vertex `v` of `Y` and `o in pi^(-1)(v)`.  Let `T = p^(-1)(v)`.  Since
`sum_(x in T) d_x = N`, we have `|T| >= N - sum_(b in B) d_b = (1 - beta) N`.
Hence

```text
#{t in T : d_X(t,B) < R} / |T| <= (c_Y v_Delta(R) + 1) beta / (1 - beta).   (BR)
```

## Step 3. The induced model (part 1)

For `g in G` write `|g| = d(o, g o)`.  Let `V = q^(-1)(v)`, and set
`rho(x) = d(x, B~)`, which is `Lambda`-invariant.  For `x in V` and
`|g| < rho(x)` define

```text
g * x = dev_(x,o)^(-1)(g^(-1) o)  in V.
```

**Lemma 4.**
1. If `|g| + |h| + |hg| < rho(x)`, then `h * (g * x) = (hg) * x`.
2. If `g * x = x`, then `g = 1`.
3. `g * (lambda x) = lambda (g * x)` for `lambda in Lambda`.

*Proof.*  Let `x' = g * x`.  By Lemma 2.3,
`dev_(x', g^(-1) o) = dev_(x,o)` on `B(x', rho(x) - |g|)`.  By Lemma 2.2,
`dev_(x',o) = g dev_(x', g^(-1) o)`.  Then

```text
h * x' = dev_(x',o)^(-1)(h^(-1) o) = dev_(x,o)^(-1)(g^(-1) h^(-1) o) = (hg) * x.
```

Part 2 follows because `G` acts freely on `Delta` and `dev` is injective.
Part 3 is Lemma 2.1.  QED

Now fix a finite `F subset G` containing 1 and `epsilon > 0`.  Let
`D = 3 max_(g in F) |g| + 1`.  Choose `X` with `beta = beta(X)` so small that
`(BR)` with `R = D` is below `epsilon / 2`, and with `Lambda` sofic.

Let `T~ subset V` be a set of lifts of `T`, one per `Lambda`-orbit.  For
`t in T~` with `rho(t) >= D` and `g in F F`, write uniquely
`g * t = lambda(t,g) tau(t,g)` with `lambda(t,g) in Lambda` and
`tau(t,g) in T~`.  Let `E subset Lambda` be the finite set of all
`lambda(t,g)^(+-1)` and their pairwise products.

Take a sofic model of `Lambda` for `(E, epsilon/2)`: a finite set `M`, maps
`sigma: E -> Sym(M)`, and `M_0 subset M` with `|M_0| >= (1 - epsilon/2) |M|`,
such that for `m in M_0`:

* `sigma(mu) sigma(nu) m = sigma(mu nu) m` whenever `mu, nu, mu nu in E`;
* `sigma(mu) m != m` for `mu in E \ {1}`.

Set `Omega = M x T~`.  For `g in F F` define the partial map

```text
Sigma(g)(m,t) = ( sigma(lambda(t,g)^(-1)) m , tau(t,g) )   if rho(t) > |g| ,
```

and complete it to a permutation of `Omega` arbitrarily.  (Lemma 4.3 and
the injectivity of `g *` show that the partial map is injective.)  Call
`(m,t)` good if `m in M_0` and `rho(t) >= D`.  By `(BR)` the good fraction
is at least `(1 - epsilon/2)^2 >= 1 - epsilon`.

*Multiplicativity.*  Let `(m,t)` be good and `g, h, hg in F`.  Write
`g * t = lambda_1 tau_1`.  Then `rho(tau_1) >= D - |g| > |h|`, so write
`h * tau_1 = lambda_2 tau_2`.  By Lemma 4.3 and 4.1,

```text
(hg) * t = h * (lambda_1 tau_1) = lambda_1 lambda_2 tau_2 .
```

So `lambda(t,hg) = lambda_1 lambda_2` and

```text
Sigma(h) Sigma(g) (m,t) = (sigma(lambda_2^(-1)) sigma(lambda_1^(-1)) m, tau_2)
                        = (sigma((lambda_1 lambda_2)^(-1)) m, tau_2) = Sigma(hg)(m,t).
```

*Freeness.*  Let `g in F \ {1}` and suppose `Sigma(g)(m,t) = (m,t)`.  Then
`tau(t,g) = t`.  If `lambda(t,g) = 1`, then `g * t = t`, contradicting
Lemma 4.2.  So `lambda = lambda(t,g) in E \ {1}`, and `sigma(lambda^(-1)) m = m`
contradicts `m in M_0`.

Thus `(Omega, Sigma)` is an `(F, epsilon)`-sofic model of `G`.  Since `F`
and `epsilon` were arbitrary, `G` is sofic.  If `Lambda` is residually
finite, `M` can be taken to be a finite quotient in which `E` injects, with
`M_0 = M`.

## Step 4. Sparse branched covers from sofic models (part 2)

Cells are understood as in B--H I.7, glued by characteristic maps that need
not be injective on the boundary.  Let `Y°` be `Y` with its vertices
removed.  It deformation retracts onto a finite graph, so `pi_1(Y°, *)` is
free on some `f_1, ..., f_k`.

Van Kampen, applied to `Y = Y° cup (cone neighbourhoods of the vertices)`,
gives three facts:
* `pi_1(Y°) -> G` is onto;
* its kernel is normally generated by the words
  `w_(y,j) = gamma_y l_(y,j) gamma_y^(-1)`, where `l_(y,j)` runs over a finite
  free basis of `pi_1(S_y)`, with `S_y ≅ Lk(y)` a small link sphere about
  `y` and `gamma_y` a path from `*` to `S_y`;
* each `w_(y,j)` is trivial in `G`.

Let `k_i` be the image of `f_i` in `G`.  Let `L` be the total length of all
`w_(y,j)` as words in the `f_i`.

Let `(Sigma, [n])` be an `(F', epsilon)`-sofic model of `G`, where `F'`
contains all the `k_i^(+-1)` and the images of all subwords of the
`w_(y,j)`.  Chaining the multiplicativity identity along a word shows that
the permutation `Sigma(w_(y,j))`, obtained by substituting
`Sigma(k_i)^(+-1)` for the letters, fixes all but at most
`(L + 1) epsilon n` points.

The assignment `f_i -> Sigma(k_i)` defines an action of the free group
`pi_1(Y°)` on `[n]`.  It defines an `n`-sheeted covering `X°_n -> Y°`.

Over the punctured cone neighbourhood `C(Lk y) \ {y} = Lk(y) x (0, epsilon]`,
the covering is a disjoint union of `L_c x (0, epsilon]`, one for each
connected covering `L_c -> Lk(y)`.  The components `L_c` correspond to
orbits of `pi_1(S_y)` on the fibre, transported along `gamma_y`, and `d_c`
is the orbit size.  Adding one cone point to each component gives a finite
branched cover `X_n -> Y` with `Lk(x_c) = L_c`.

An orbit of size `d_c > 1` is a nontrivial transitive action, so each of its
points is moved by some basis loop, that is by some `Sigma(w_(y,j))`.
Therefore

```text
beta(X_n) n = sum_(b in B) d_b <= sum_(y,j) |supp Sigma(w_(y,j))| <= (#words) (L+1) epsilon n .
```

Letting `epsilon -> 0` gives `beta(X_n) -> 0`.  QED

## What is not proved

Part 2 says nothing about `pi_1(X_n)`.  The covers it produces are arbitrary
monodromy completions, and their fundamental groups need not be sofic.
Parts 1 and 2 therefore do not combine to an equivalence.
