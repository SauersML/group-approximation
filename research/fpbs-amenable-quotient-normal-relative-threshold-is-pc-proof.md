---
rg: 2
id: fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof
kind: route
title: Burton--Keane trifurcation count over invariant Folner cells of the amenable quotient
target: fpbs-amenable-quotient-normal-relative-threshold-is-pc
requires:
  - fpbs-cluster-count-trichotomy
  - fpbs-relative-gap-along-any-subgroup-separates
---

Notation. `pi : Gamma -> Q = Gamma/N`, the fibre of `q in Q` is `pi^(-1)(q)`,
`o` is the identity, `B_R` is the ball of radius `R` about `o`, `E(B_R)` is the
set of edges with both endpoints in `B_R`, `S_R = B_R \ B_(R-1)`, and `K(x)` is
the open cluster of `x`. Left multiplication is a graph automorphism of `G`, so
Bernoulli percolation is invariant under it.

**Step 0. Reduction to the non-uniqueness window.**
* `p_c(G) <= p_c(N;G)`, since an `N`-infinite cluster is infinite.
* `p_c(N;G) <= p_u(G)` by `fpbs-relative-gap-along-any-subgroup-separates`.
  So if `p_c(G) = p_u(G)` we are done.
* Otherwise fix `p in (p_c(G), p_u(G))`, so `0 < p < 1` and, by
  `fpbs-cluster-count-trichotomy`, a.s. there are infinitely many infinite
  clusters. It suffices to show that an `N`-infinite cluster exists a.s.
* The event `A` = "some cluster meets `N` in infinitely many vertices" is
  invariant under left multiplication by `N`, since `nN = N`. `N` acts freely
  on vertices, so for a finite edge set `F` only finitely many `n` have
  `nF ∩ F` nonempty. Approximating `A` by events depending on finitely many
  edges and using independence gives `P_p(A) = P_p(A)^2`, so
  `P_p(A) in {0,1}`.
* Suppose `P_p(A) = 0`. Left multiplication by `x^(-1)` sends `xN` to `N`, and
  there are countably many cosets. So a.s., for every cluster `K` and every
  `q in Q`, the set `K ∩ pi^(-1)(q)` is finite. We derive a contradiction.

**Step 1. Trifurcations have positive density.** Call `t` a trifurcation if
`K(t) \ {t}` has at least three infinite components, and let
`delta = P_p(o is a trifurcation)`.
* Let `omega'` be `omega` with the edges of `E(B_R)` removed. Closing finitely
  many edges splits an infinite cluster meeting `B_R` into finitely many
  pieces, and some infinite piece meets `B_R`. Distinct clusters give distinct
  pieces. So for `R` large, with positive probability `omega'` has at least
  three infinite components meeting `B_R`. They meet `B_R` only in `S_R`,
  because vertices of `B_(R-1)` are isolated in `omega'`.
* On that event choose, by a fixed measurable rule, `w_1, w_2, w_3 in S_R` in
  distinct infinite components of `omega'`, and geodesics `gamma_i` from `o` to
  `w_i`. All their edges lie in `E(B_R)` and their vertices other than `w_i` lie
  in `B_(R-1)`.
* The union `Y'` of the `gamma_i` with `w_i` deleted is connected. Take a
  spanning tree of `Y'` and attach each `w_i` as a leaf by the last edge of
  `gamma_i`. The minimal subtree spanning three distinct leaves is a tripod with
  a center `c in B_(R-1)` of degree 3.
* Set `omega = omega'` off `E(B_R)` and `omega = 1_(tripod)` on `E(B_R)`. The
  three arms minus `c` are disjoint, their vertices other than `w_i` are
  isolated in `omega'`, and the `w_i` lie in distinct `omega'`-components. So
  `K(c) \ {c}` has three infinite components and `c` is a trifurcation.
* The configuration on `E(B_R)` has probability at least
  `min(p,1-p)^|E(B_R)|` and is independent of `omega'`. So with positive
  probability some vertex of `B_(R-1)` is a trifurcation. By the union bound
  and invariance under left multiplication, `delta > 0`.

**Step 2. Invariant Folner cells on `Q`.** Fix `epsilon > 0` and write
`S_Q = pi(S)`, a finite symmetric subset of `Q`.
* `Q` is amenable, so there is a finite `F ⊆ Q` with
  `|F Δ F t| <= epsilon |F|` for all `t in S_Q`. (Right Folner sets exist:
  invert a left Folner set.)
* Let `U = (U_c)_(c in Q)` be i.i.d. uniform on `[0,1]`, independent of
  `omega`. For `x in Q` let `c(x)` be the `c in x F^(-1)` minimising `U_c`
  (ties have probability zero). The cells are the level sets of `c`.
* **Finite cells.** `c(x) = c_0` forces `c_0 in x F^(-1)`, i.e. `x in c_0 F`.
* **Invariance.** For `g in Q`, `c_U(gx) = g c_(U∘g)(x)`, where
  `(U∘g)_c = U_(gc)` has the law of `U`. So the pair `(omega, U)`, with `Gamma`
  acting on `U` through `pi`, is invariant under left multiplication by
  `Gamma`, and so is every construction below.
* **Small boundary.** For `t in S_Q`, put `A = xF^(-1)` and `B = xtF^(-1)`, both
  of size `|F|`. If the minimiser over `A ∪ B` lies in `A ∩ B` then
  `c(x) = c(xt)`. So
  `P(c(x) != c(xt)) <= |A Δ B|/|A ∪ B| <= |F^(-1) Δ tF^(-1)|/|F| = |F Δ F t^(-1)|/|F| <= epsilon`.

**Step 3. Cutting clusters along cell walls.** Let `xi` be the set of open
edges `{x, xs}` with `c(pi(x)) = c(pi(xs))`.
* The `xi`-cluster `C(x)` of `x` lies in `K(x) ∩ pi^(-1)(cell of pi(x))`. That
  is a finite union of sets `K(x) ∩ pi^(-1)(q)`, each finite by Step 0. So every
  `xi`-cluster is finite.
* By Step 2, `E deg_(omega \ xi)(o) <= sum_(s in S) P(c(o_Q) != c(pi(s))) <= |S| epsilon`.

**Step 4. Counting lemma.** Let `T` be the set of trifurcations, `C` a finite
`xi`-cluster inside the cluster `K`, and `∂C` the set of open edges with
exactly one endpoint in `C`. Then `|T ∩ C| <= |∂C|`, and `∂C ⊆ omega \ xi`.
* `∂C ⊆ omega \ xi`: an edge of `xi` at a vertex of `C` has both endpoints in
  `C`.
* Assume `T ∩ C` is nonempty, so `K` is infinite. Let `H` be the finite graph
  obtained from `K` by contracting each component `D` of `K \ C` to one vertex.
  `K` is connected and `C` is nonempty, so every `D` is joined to `C` by an edge
  of `∂C`. Hence the set `Y` of infinite components `D` has `|Y| <= |∂C|`.
* Let `t in T ∩ C`. Each `D` is connected in `K \ {t}`, so lies in one
  component of `K \ {t}`. An infinite component of `K \ {t}` contains infinitely
  many vertices outside the finite set `C`, spread over at most `|∂C|` sets `D`.
  So it contains some infinite `D`. Distinct components of `K \ {t}` give
  distinct components of `H \ {t}`. So `t` separates at least three vertices of
  `Y` in `H`, and `|Y| >= 3`.
* Take a spanning tree of `H` and its minimal subtree `tau` spanning `Y`. The
  leaves of `tau` lie in `Y`. For each `t in T ∩ C`, the tree paths from `t` to
  three `Y`-vertices in distinct components of `H \ {t}` leave `t` by distinct
  edges. So `t` has degree at least 3 in `tau`.
* A finite tree with `L` leaves has at most `L - 2` vertices of degree at least
  3. So `|T ∩ C| <= |Y| - 2 < |∂C|`.

**Step 5. Mass transport.** `Gamma` is unimodular, and the process
`(omega, U)` is invariant under left multiplication. So the mass-transport
principle applies to every invariant function `f(x,y)`:
`E sum_y f(o,y) = E sum_x f(x,o)`.
* With `f(x,y) = 1{x in T} 1{y in C(x)} / |C(x)|`, which is well defined
  because `C(x)` is finite:
  `delta = E |T ∩ C(o)| / |C(o)|`.
* With `g(x,y) = 1{y in C(x)} b(x) / |C(x)|`, where `b(x)` is the number of
  edges of `∂C(x)` at `x`:
  `E |∂C(o)| / |C(o)| = E b(o) <= E deg_(omega \ xi)(o)`.
* Steps 3 and 4 give `delta <= E |∂C(o)|/|C(o)| <= |S| epsilon`. Since
  `epsilon > 0` was arbitrary, `delta = 0`, contradicting Step 1.

**Conclusion.** `P_p(A) = 1` for every `p in (p_c(G), p_u(G))`, so
`p_c(N;G) <= p_c(G)`. With Step 0 this gives `p_c(N;G) = p_c(G)`.

**Corollaries.**
* For `I` containing an infinite normal `N` with amenable `Gamma/N` (in
  particular `N = core(I)`), an `N`-infinite cluster is `I`-infinite. So
  `p_c(G) <= p_c(I;G) <= p_c(N;G) = p_c(G)`.
* By the equivalence of conditions 1 and 2 in
  `fpbs-relative-gap-along-any-subgroup-separates`, `chi^I_p = infinity` for
  every `p > p_c(G)`.
* The contrapositive gives Corollary 2 of the claim, and the definition of
  normal co-amenability gives Corollary 3.

**Where normality is used.** The set `x F^(-1)` and the invariance in Step 2
need the left `Gamma`-action on `Q` to be multiplication in a group, so that
`c(x)` and `c(xt)` are compared through the fixed set `F`. For a coset space
`Gamma/H` that is not a group, an equivariant family of finite windows with
small boundary is exactly what is missing.



