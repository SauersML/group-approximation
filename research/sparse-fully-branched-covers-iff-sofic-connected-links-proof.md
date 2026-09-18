---
rg: 2
id: sparse-fully-branched-covers-iff-sofic-connected-links-proof
kind: route
title: Links are forced connected by any cover; under connected links rebuild the monodromy cover with honest bookkeeping, then run the trivial-model descent for the mark
target: sparse-fully-branched-covers-iff-sofic-with-connected-links
requires:
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - infinite-simple-group-permutation-stable-iff-nonsofic
  - finite-branched-covers-force-connected-vertex-links
---

This is the argument of `sparse-fully-branched-covers-iff-sofic-proof`
(Steps A, C and the Step B orbit argument checked by three referees in
swarm-0917) with its one gap closed.  That gap was the import, in Step B,
of Step 4 of `sparse-branched-covers-sofic-pi1-reduction-proof`, which needs
connected vertex links.  Here the link hypothesis is part of item 1, it is
free for items 2 and 3 by `finite-branched-covers-force-connected-vertex-links`,
and Step 4 is redone under it (Step B0).  The steps are written out in full
so that this route does not lean on the text of the invalidated one.

**Imports.**  From `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`
and its proof `sparse-branched-covers-sofic-pi1-reduction-proof`: Part 3
(every finite branched cover is locally CAT(0), so each component has CAT(0)
universal cover), Lemmas 1--4 of Steps 1 and 3, and the bound `(BR)` of
Step 2.  None of these uses connectivity of the links of `Y` or Part 2 of
that claim; they are statements about a given cover `X` and hold for each
component of a disconnected `X`.  Notation from there: `q: X~ -> X -> Y`,
`pi: Delta -> Y`, a fixed vertex `v` of `Y` and `o in pi^(-1)(v)`,
`V = q^(-1)(v)`, `rho(x) = d(x, B~)`, `|g| = d(o, g o)`, `g * x` for
`|g| < rho(x)`, and `Lambda` the deck group of a component.  Also
`kappa: X~ -> X` is the universal covering of a component, so the fibres of
`kappa` on `V` are the `Lambda`-orbits.

**Sofic models.**  For finite `F subset G` with `1 in F = F^(-1)` and
`epsilon > 0`, an `(F, epsilon)`-model is a map `Sigma: F -> Sym(n)` with
`Sigma(1) = id` such that, for `g, h, gh in F`, `Sigma(g) Sigma(h)` and
`Sigma(gh)` differ on at most `epsilon n` points, and each `Sigma(g)`,
`g in F \ {1}`, has at most `epsilon n` fixed points.  `G` is sofic if and
only if such models exist for all `F, epsilon` (the normalization
`Sigma(1) = id` costs a constant factor in `epsilon`).  `K` and `G` are sofic
together, since soficity passes to subgroups and to finite-index
overgroups.  `d_H` is the normalized Hamming distance.

## Step A. 3 => 1

*Links.*  Each `X_n` is nonempty, so by
`finite-branched-covers-force-connected-vertex-links` (Part 1) every vertex
link of `Y` is connected.  It remains to show that `K` is sofic.

*The almost homomorphism.*  Let `N_n` be the sheet number of `X_n` and
`T_n = p^(-1)(v)`.  Choose `D_n -> infinity` so slowly that
`(c_Y v_Delta(D_n) + 1) beta(X_n) / (1 - beta(X_n)) -> 0`.  Call `t in T_n`
*good* if `rho(t~) >= D_n` for a (any) lift `t~ in V`; this is
`d_X(t, B) >= D_n`, since `kappa` is a local isometry off `B~` and
shortest paths lift.  By `(BR)` the good fraction of `T_n` tends to 1.

For `g in G` and `t in T_n` with `rho(t~) > 2|g|` put

```text
Sigma_n(g)(t) = kappa(g * t~) .
```

It does not depend on the lift (Lemma 4.3).  It is injective on its domain:
if `kappa(g * x) = kappa(g * x')`, then `g * x' = lambda (g * x) = g * (lambda x)`
by Lemma 4.3, and since `rho(g * x) >= rho(x) - |g| > |g|`, Lemma 4.1 with
`h = g^(-1)` gives `g^(-1) * (g * x) = x`, so `x' = lambda x`.  Extend
`Sigma_n(g)` to a permutation of `T_n` arbitrarily.

Fix `g, h`.  Once `D_n > 3(|g| + |h| + |hg|)`, at a good `t` write
`x = t~`.  Then `rho(g * x) > 2|h|`, so
`Sigma_n(h) Sigma_n(g) t = kappa(h * (g * x)) = kappa((hg) * x) = Sigma_n(hg) t`
by Lemma 4.1.  Hence `d_H(Sigma_n(h) Sigma_n(g), Sigma_n(hg)) -> 0`, and
`Sigma_n|_K` is an almost homomorphism of `K` in the sense of
`infinite-simple-group-permutation-stable-iff-nonsofic`.  (This is Step 3 of
the reduction with the one-point model of `Lambda`; freeness is not claimed.)

*Descent.*  `K` has finite index in `G`, so it acts cocompactly on `Delta`.
Fix `r_0 > 0` such that the `K`-translates of the open ball `B(o, r_0)`
cover `Delta`, and put `F_K = {k in K : |k| < 2 r_0}`, a finite set.

**Lemma 5.**  Let `x in V` with `rho = rho(x) > 5 r_0`, and suppose
`kappa(k * x) = kappa(x)` for every `k in F_K`.  Then the component of `X`
containing `kappa(x)` is unbranched.

*Proof.*  Put `dev = dev_(x,o)` (Lemma 1) and
`psi = kappa o dev^(-1): B(o, rho) -> X`, a local isometry into `X \ B` with
`p o psi = pi`.

*Invariance.*  Let `k in F_K`, so `k * x = lambda x` for some
`lambda in Lambda`, and `d(x, lambda x) = |k|`.  By Lemmas 2.3 and 2.2,
`dev_(lambda x, o) = k o dev_(lambda x, k^(-1) o) = k o dev` on
`B(lambda x, rho - |k|)`.  By Lemma 2.1, `dev_(lambda x, o) = dev o lambda^(-1)`
there.  So `dev(lambda^(-1) a) = k dev(a)` for `a in B(x, rho - 2|k|)`, a
set inside `B(lambda x, rho - |k|)`.  Apply `kappa`, with
`kappa o lambda^(-1) = kappa`:

```text
psi(k z) = psi(z)     for all z in B(o, rho - 2|k|).                 (INV)
```

*Descent.*  For `z in Delta` pick `k in K` with `k z in B(o, r_0)` and set
`s(z) = psi(k z)`.  If `k'` also works, put `h = k' k^(-1)` and `w = k z`.
Then `|h| <= d(o, h w) + d(h w, h o) < 2 r_0`, so `h in F_K`, and
`w in B(o, r_0) subset B(o, rho - 2|h|)` because `rho > 5 r_0`.  By (INV),
`psi(h w) = psi(w)`, so `s` is well defined.  Near `z` the same `k` works,
so `s` is locally `psi o k`: a `K`-invariant local homeomorphism
`Delta -> X \ B`.  Its image is open, compact (the image of `Delta / K`),
connected, and contains `s(o) = kappa(x)`.  So it is the whole component
of `kappa(x)`, and that component misses `B`.  QED

*The mark.*  A component `C` with `N_C` sheets has between
`N_C - sum_(b in B cap C) d_b` and `N_C` points of `T_n`, and
`sum_b d_b = beta(X_n) N_n = o(|T_n|)` because `|T_n| >= (1 - beta) N_n`.
So at least a fraction `c - o(1)` of `T_n` is good and lies in branched
components.  Once `D_n > 5 r_0`, for `k in F_K` the permutation
`Sigma_n(k)` is given by the formula at every good point, since
`2|k| < 4 r_0`.  By Lemma 5, each good `t` in a branched component is moved
by `Sigma_n(k)` for some `k in F_K \ {1}`.  So some `k_n in F_K \ {1}` has
`d_H(Sigma_n(k_n), 1) >= (c - o(1)) / |F_K|`.  `F_K` is finite, so one `k`
occurs for infinitely many `n`.  Along that subsequence `Sigma_n|_K` is an
almost homomorphism with `d_H(Sigma_n(k), 1) >= c / (2|F_K|)` for large `n`.
By `infinite-simple-group-permutation-stable-iff-nonsofic` ((1) => (2),
contrapositively), `K` is sofic.

## Step B0. Sparse covers from sofic models, under connected links

Assume every vertex link of `Y` is connected and nonempty.  Cells are as in
B--H I.7.  Choose `epsilon_0 > 0` so small that the closed cone
neighbourhoods `C_y = C_(epsilon_0)(Lk y)` of distinct vertices are disjoint
and each is a Euclidean cone; `C_y \ {y} ≅ Lk(y) x (0, epsilon_0]`.  Let
`Y°` be `Y` minus its vertices.

*(a) `Y°` is connected.*  Suppose `Y° = U ⊔ U'` with `U, U'` open and
nonempty.  Each `C_y \ {y}` is connected (`Lk y` is), so it lies in `U` or
in `U'`.  Adding to `U` the open cones `int C_y` of the vertices whose
punctured cones lie in `U`, and likewise for `U'`, splits `Y` into two
disjoint nonempty open sets, contradicting connectedness.

*(b) `pi_1(Y°)` is free of finite rank.*  Radial retraction of each
punctured cone `C_y \ {y}` onto its boundary sphere is a deformation
retraction of `Y°` onto the compact complex `Y_1 = Y \ union int C_y`.  In
`Y_1` each 1-cell becomes a closed segment `sigma_e`, and each 2-cell a
disk `D` whose boundary alternates between segments `sigma_e` of its sides
and arcs of the spheres `S_y`; those arcs lie in no other cell.  Joining
the barycentre of `D` to the midpoints of its side segments cuts `D` into
disks, each with one such free arc in its boundary, and a disk deformation
retracts onto the closure of the complement of an open boundary arc.  So
`D` deformation retracts, relative to its side segments, onto their union
with this star.  Hence `Y_1`, and so `Y°`, deformation retracts onto a
finite graph, connected by (a).  So `pi_1(Y°, *)` is free on some
`f_1, ..., f_k`.

*(c) Van Kampen.*  `Y = Y° cup (union of int C_y)`, the pieces
`int C_y` are contractible, and each intersection `int C_y \ {y}` is path
connected with free fundamental group `pi_1(S_y) ≅ pi_1(Lk y)` of finite
rank, `S_y` being a link sphere at radius `epsilon_0 / 2`.  Fix a path
`gamma_y` in `Y°` from `*` to a base point `s_y in S_y` (it exists by (a))
and a free basis `l_(y,1), ..., l_(y,m_y)` of `pi_1(S_y, s_y)` (`m_y = 0` if
`Lk y` is a tree).  Van Kampen, applied once for each vertex, gives that
`pi_1(Y°) -> G` is onto, with kernel the normal closure of the words
`w_(y,j) = gamma_y l_(y,j) gamma_y^(-1)`, written in the `f_i^(+-1)`.  Let
`k_i in G` be the image of `f_i`, `L` the sum of the lengths of all
`w_(y,j)`, and `W` their number.

*(d) Word bookkeeping.*  Let `Sigma` be an `(F', epsilon)`-model on `[n]`
(`F'` symmetric, containing 1) and `phi: pi_1(Y°) -> Sym(n)` the
homomorphism with `phi(f_i) = Sigma(k_i)`.  Let `u = a_1 ... a_l` be a word
in the `f_i^(+-1)` such that `F'` contains the images `ā_j` of the letters
and `g_j` of the prefixes `a_1 ... a_j`, with image `g = g_l`.  Then

```text
#{ m : phi(u) m != Sigma(g) m } <= 2 l epsilon n .                  (W)
```

*Proof.*  For a letter `a = f^(-1)` with image `ā = k^(-1)`:
`Sigma(k) Sigma(k^(-1))` agrees with `Sigma(1) = id` off `epsilon n`
points, and at the others `Sigma(k^(-1)) m = Sigma(k)^(-1) m`.  So
`phi(a)` and `Sigma(ā)` differ on at most `epsilon n` points for every
letter.  Put `P_j = phi(a_1 ... a_j)`.  If `P_(j-1)` and `Sigma(g_(j-1))`
differ on at most `2(j-1) epsilon n` points, then `P_j = P_(j-1) phi(a_j)`
and `Sigma(g_(j-1)) Sigma(ā_j)` differ on at most
`epsilon n + 2(j-1) epsilon n` points (a point `m` is bad only if
`phi(a_j) m != Sigma(ā_j) m`, or if `Sigma(ā_j) m` is bad for the previous
pair), and `Sigma(g_(j-1)) Sigma(ā_j)` differs from `Sigma(g_j)` on at most
`epsilon n` points.  Induct.  QED

*(e) The cover.*  Let `G` be sofic and take `F'` containing the `k_i^(+-1)`
and the images of all prefixes of all `w_(y,j)`.  Let `Sigma` be an
`(F', epsilon)`-model on `[n]` and `phi` as in (d).  Let `X°_n -> Y°` be the
`n`-sheeted covering with fibre `[n]` over `*` and monodromy given by the
right action `m . f = phi(f)^(-1) m`; its sheets over `*` are permuted by
the loop `f` exactly as `phi(f)^(-1)` does, and its components correspond
to the orbits of `phi(pi_1(Y°))` on `[n]`.  Since each `w_(y,j)` has image
`1` in `G` and `Sigma(1) = id`, (W) gives

```text
|supp phi(w_(y,j))| <= 2 |w_(y,j)| epsilon n .
```

Over `int C_y \ {y} ≅ Lk(y) x (0, epsilon_0)` the covering splits as a
disjoint union of `L_c x (0, epsilon_0)`, one for each orbit `c` of the
subgroup `H_y = gamma_y pi_1(S_y) gamma_y^(-1)` on `[n]` (identified with
the fibre over `s_y` by transport along `gamma_y`).  Here `L_c` is a
connected covering of `Lk(y)` of degree `d_c = |c|`, because the second
factor is contractible and `Lk(y)` is connected.  Add one cone point `x_c`
for each `c`.

*(f) `X_n` is a finite branched cover.*  Let `X_n` be `X°_n` with these
cone points, topologized so that `(L_c x (0, epsilon_0)) ∪ {x_c}` is the
open cone on `L_c`.  For a closed cell `P -> Y` (a polygon or a segment),
`P` minus its corners is contractible (it is star-shaped about an interior
point), so its map to `Y°` lifts to `X°_n` in exactly `n` ways.  Near a
corner mapping to `y`, a lift runs into one piece `L_c x (0, epsilon_0)`,
so it extends continuously over the corner by `x_c`.  Thus `X_n` is the
union of `n` copies of each closed cell of `Y`, glued along lifts of edges
and at cone points, and `p` maps each closed cell isometrically onto a
closed cell.  The link of `x_c` is `L_c`, which is connected and covers
`Lk(y)` with degree `d_c >= 1`; off the cone points `p` is the `n`-sheeted
covering `X°_n -> Y°`.  So `X_n` is a nonempty finite branched cover in the
sense of the Setting, with `N = n`.  Its components correspond to the
orbits of `phi(pi_1(Y°))`: a cone point lies over one connected piece
`L_c x (0, epsilon_0)`, so adding it merges no components.

*(g) Mass.*  A point of an `H_y`-orbit of size `d_c > 1` is moved by some
generator `phi(w_(y,j))` of `phi(H_y)`.  Distinct `c` over the same `y` are
disjoint.  So

```text
beta(X_n) n = sum_(b in B) d_b <= sum_(y,j) |supp phi(w_(y,j))| <= 2 L epsilon n .   (M)
```

Letting `epsilon -> 0` gives nonempty finite branched covers with
`beta -> 0`.  This proves the repaired Part 2 stated in the target, and,
together with `finite-branched-covers-force-connected-vertex-links`,
identifies exactly when Part 2 of
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` holds: for sofic
`G`, sparse (indeed any) finite branched covers exist if and only if every
vertex link of `Y` is connected.

## Step B. 1 => 2

Assume 1 and fix `eta > 0`.  Fix `g in K \ {1}` and a word `u` of length `l`
in the `f_i^(+-1)` with image `g`; it exists because `pi_1(Y°) -> G` is onto
by Step B0 (c).  Run Step B0 (e)--(g) with `F'` also containing `g` and the
images of all prefixes and letters of `u`.  This gives `X_n` with
`beta(X_n) <= 2 L epsilon`, whose components are the orbits `O` of
`phi(pi_1(Y°))` on `[n]`.

*Unbranched orbits are fixed by `phi(u)`.*  Let `O` be the orbit of an
unbranched component.
* Every cone point of it has degree 1, so every `H_y`-orbit meeting `O` is
  a singleton, and every `phi(w_(y,j))` fixes `O` pointwise.
* `O` is `phi`-invariant, so every conjugate `phi(f w_(y,j) f^(-1))` fixes
  `O` pointwise too, and the action of `pi_1(Y°)` on `O` kills the normal
  closure of the `w_(y,j)`, which is the kernel of `pi_1(Y°) -> G`.  So it
  factors through a homomorphism `G -> Sym(O)`.
* The kernel of its restriction to `K` is normal in the simple group `K`,
  and it is not trivial because `K` is infinite and `Sym(O)` is finite.  So
  `K` acts trivially on `O`.
Hence `phi(u)`, which acts on `O` as `g in K`, fixes `O` pointwise.

*Few points in unbranched orbits.*  By (W), `phi(u)` and `Sigma(g)` differ
on at most `2 l epsilon n` points, and `Sigma(g)` has at most `epsilon n`
fixed points since `g in F' \ {1}`.  So `phi(u)` fixes at most
`(2l + 1) epsilon n` points, and at most that many points lie in unbranched
orbits.

*Remove them.*  Deleting the unbranched components leaves a fully branched
finite branched cover `X'_n` with the same branch set and at least
`(1 - (2l+1) epsilon) n > 0` sheets, so it is nonempty and

```text
beta(X'_n) <= 2 L epsilon / (1 - (2l + 1) epsilon) .
```

For `epsilon` small this is below `eta`.

## Step C. 2 => 3

Immediate, with `c = 1`.

## Summary

Step A gives 3 => 1, Step B gives 1 => 2 (using connected links through
Step B0), and Step C gives 2 => 3.  The Corollary is the case where the
link clause of item 1 holds automatically.  QED
