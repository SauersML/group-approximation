---
rg: 2
id: bounded-area-commuting-conjugator-localization-proof
kind: route
title: Glue the van Kampen disk of [y,h] into an annulus over <h>\X; free-edge preimages are inessential curves, so the anchored part joins the two ends
target: bounded-area-commuting-conjugator-localization
requires: []
---

Elementary; the only inputs are van Kampen's lemma and covering-space theory.

## 0. Set-up

`X` is the Cayley 2-complex of `<S | R>`, simply connected, with 1-skeleton
`Cay(Gamma,S)`.  `<h>` acts on `X` from the left.

**The action is free.**  A vertex fixed by `h^m` gives `h^m = 1`.  An edge
flipped by `h^m` has both endpoints fixed by `h^(2m)`.  A 2-cell mapped to
itself by `h^m` rotates its boundary loop, which reads a relator `u^p`: then
`h^m g = g u^j`, so `h^m` is conjugate to `u^j`, and `u` has finite order.
In a torsion-free group each case forces `h^m = 1`, hence `m = 0`, because
`h != 1` has infinite order.  So `q : X -> Xbar := <h>\X` is a covering map,
`pi_1(Xbar, q(1)) = <h> = Z`, and the loop `q(path of h from 1)`
represents the generator.  `Xbar^(1)` is the Schreier graph on left cosets
`<h>g`, with edges `<h>g -> <h>gs`.

## 1. The diagram

Let `W = y h y^(-1) h^(-1)` and let `D` be a van Kampen diagram for `W` with
at most `A` two-cells.  Let `pi : D -> X` be the label-preserving map with
base vertex `O -> 1`.  The boundary cycle, read from `O`, is

```text
alpha (reads y, O -> Q),  beta_1 (reads h, Q -> Q'),
alpha' (reads y^(-1), Q' -> O'),  beta_2^(-1) (reads h^(-1), O' -> O).
```

So `pi(O') = h`, `pi(Q) = y` and `pi(Q') = yh`.  Read backwards, `alpha'`
is a path reading `y` from `O'` to `Q'`.  For `1 <= i <= |y|`, call the `i`-th
edge of `alpha` the slot `(y,i)`, and the `i`-th edge of reversed `alpha'` the
slot `(y',i)`.  Then `pi(slot (y',i)) = h * pi(slot (y,i))`, so

```text
q pi (slot (y,i)) = q pi (slot (y',i))   as oriented edges of Xbar.     (1.1)
```

Let `Z ⊂ D` be the union of the closed 2-cells and the paths `beta_1`,
`beta_2`.  It has at most `A M + 2|h|` edges.  Every edge of `D` outside
`Z` lies on the boundary cycle but on no 2-cell and on neither `beta`.  So it
occurs only in slots of `alpha` or `alpha'`; call such an edge *free*.

## 2. The annulus

Embed `D` in the plane and let `B = N(D)` be a closed regular neighbourhood.
It is a closed disk, since `D` is compact, planar and contractible, and it
comes with the standard retraction `rho : B -> D`.  `rho` maps `∂B` onto the
boundary cycle, so `∂B` is cut into the arcs `alpha, beta_1, alpha', beta_2`.

`rho` is a homeomorphism over the interiors of the 2-cells.  Take a point `p`
in the interior of an edge `e` that lies on no 2-cell.  Then `rho^(-1)(p)` is
a single arc, the *chord* of `p`.  The chord crosses `B` and meets `∂B` only
at its two endpoints, which are the points above `p` in the two boundary
slots of `e`.

Parametrise every edge linearly.  By (1.1), the map `F = q pi rho : B -> Xbar`
agrees at corresponding points of `alpha` and of reversed `alpha'`.  Glue
`alpha` to `alpha'` by that correspondence, `O ~ O'` and `Q ~ Q'`.  The
boundary word has the shape `a b a^(-1) c`, so the quotient `Ann` is a closed
annulus, and `F` descends to `Fbar : Ann -> Xbar`.  Write `sigma` for the
image of `alpha`, the *seam*.  The boundary circles of `Ann` are `b_1`
(`beta_1` closed up) and `b_2` (`beta_2` closed up).
`Fbar(b_2) = q(path of h from 1)` is a loop representing the generator `h`
of `pi_1(Xbar) = Z`.

## 3. Preimages of free points

Let `Wim = q pi (D)`, a finite subcomplex of `Xbar`, and let
`Zhat = q pi (Z)`.  Let `ehat` be an edge of `Wim` not contained in `Zhat`,
and let `x` be an interior point of `ehat`.

Every edge `e` of `D` with `q pi(e) = ehat` is free, since `e ⊂ Z` would
give `ehat ⊂ Zhat`.  No 2-cell interior maps to `x`.  So `F^(-1)(x) ⊂ B` is
a disjoint union of chords, one for each free edge over `ehat`.  All chord
endpoints are slot points on `alpha ∪ alpha'`.

By (1.1), a slot point of `(y,i)` lies over `x` exactly when the
corresponding slot point of `(y',i)` does.  Both slot edges are then free, so
after gluing each seam point of `Fbar^(-1)(x)` is the endpoint of exactly
one chord from each side.  If one chord supplies both ends, it closes up by
itself.  Hence

```text
Fbar^(-1)(x) is a finite disjoint union of simple closed curves in int(Ann).   (3.1)
```

**No curve is essential.**  Suppose a component `gamma` were essential.
Then it is freely homotopic to `b_2`, up to orientation.  `Fbar(gamma) = x`
is constant, so `Fbar(b_2)` would be freely null-homotopic in `Xbar`.  But
`pi_1(Xbar) = Z` is abelian and `Fbar(b_2)` represents `h != 0`, a
contradiction.  So every component of (3.1) bounds a disk in `int(Ann)`.

## 4. The anchored part joins the two ends

Let `Zhat_0` be the component of `Zhat` that contains `q(1)`.  It also
contains `Fbar(b_2) = q pi(beta_2)`, because that set is connected and
contains `q(1)`.  Suppose, for a contradiction, that `q(y) = q pi(Q)` is not
in `Zhat_0`.  Let `Zhat_1` be the component of `Zhat` that contains `q(y)`,
and hence all of `Fbar(b_1)`.

Choose one interior point `x_e` on each of the finitely many edges of `Wim`
not in `Zhat`, and let `P` be the set of these points.  By §3,
`Fbar^(-1)(P)` is a finite disjoint union of simple closed curves in
`int(Ann)`, each bounding a disk.  The outermost of these disks are pairwise
disjoint closed disks in the interior of the annulus.  Their complement is
connected and contains `b_1` and `b_2`.  So there is a path `s` in `Ann` from
`b_2` to `b_1` that avoids `Fbar^(-1)(P)`.

`Fbar(s)` is then a path in `Wim \ P` from `Zhat_0` to `Zhat_1`.  But
`Wim \ P` is the disjoint union of the following relatively open and closed
sets:

- for each component `Zhat_j` of `Zhat`, the set `Zhat_j` together with the
  half-edges, cut at `P`, of the non-`Zhat` edges at its vertices;
- for each vertex outside `Zhat`, the star of half-edges at that vertex.

So `Zhat_0` and `Zhat_1` lie in different components of `Wim \ P`, which is
a contradiction.

Hence `q(1)` and `q(y)` are joined by an edge path in `Zhat_0`.  Its length
is at most the number of edges of `Zhat`, which is at most `A M + 2|h| = K`.

## 5. Conclusion

Lift that path through the covering `Cay(Gamma,S) -> Xbar^(1)`, starting at
`1`.  The lift reads a word `g` with `|g| <= K` and ends at a vertex over
`q(y) = <h>y`, so `g = h^m y` for some `m`.  Thus `y = h^(-m) g`.  Since `y`
commutes with `h`, so does `g`, which proves (LOC).

## Checks

- `y` need not be reduced; `D` exists for any null-homotopic word.
- Sanity check in `Z^2 = <a,b | [a,b]>` with `h = a` and `y = b^n a^m`:
  `Area = n`, and (LOC) gives `y = a^m b^n` with `|b^n| = n <= A M + 2`,
  which is consistent.
- Torsion-freeness is used only to make the `<h>`-action free, so that
  `pi_1(Xbar) = <h>`.
