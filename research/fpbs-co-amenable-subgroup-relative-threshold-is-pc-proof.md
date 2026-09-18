---
rg: 2
id: fpbs-co-amenable-subgroup-relative-threshold-is-pc-proof
kind: route
title: Trifurcation count over deterministic Schreier Folner fibres, with mass transport along the free action of the subgroup, then sprinkling onto the subgroup
target: fpbs-co-amenable-subgroup-relative-threshold-is-pc
requires:
  - fpbs-cluster-count-trichotomy
  - fpbs-relative-gap-along-any-subgroup-separates
---

**Notation.** `o = e`. `K(x)` is the open cluster of `x`. Left multiplication
by `g` is a graph automorphism of `G` and preserves Bernoulli percolation.
`X = I\Gamma` is the set of right cosets, and `pi : Gamma -> X`,
`pi(x) = Ix`. The **fibre** of `phi in X` is `pi^(-1)(phi)`, an orbit of the
left action of `I`. `I` acts freely on vertices by left multiplication and
preserves every fibre. For `F ⊆ X` finite, `∂F` is the set of arcs `(phi,s)`
with `phi in F`, `s in S`, `phi s ∉ F`.

The key difference from `fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof`
is that nothing here needs to be invariant under all of `Gamma`. Every
construction is invariant under left multiplication by `I` only, and
the fibres of `pi` are exactly the `I`-orbits. The one input from all of
`Gamma` is that the trifurcation density is the same at every vertex.

## Step 0. Folner sets in the Schreier graph

**Lemma 0.** If `I` is co-amenable, then for every `epsilon > 0` there is a
finite nonempty `F ⊆ X` with `|∂F| <= epsilon |F|`.

*Proof (Day, Namioka).*
1. For `f in ℓ^1(X)` and `s in S` put `(f.s)(phi) = f(phi s^(-1))`. This is a
   right action by isometries. Let `m` be the invariant mean. Invariance means
   `m(h_s) = m(h)`, where `h_s(phi) = h(phi s)`.
2. Finitely supported probability vectors are weak-* dense in the means on
   `ℓ^∞(X)`. Take a net `f_a -> m` weak-*. For every `h in ℓ^∞(X)`,
   `<f_a.s - f_a, h> = <f_a, h_s - h> -> m(h_s) - m(h) = 0`. So the vector
   `(f_a.s - f_a)_(s in S)` tends to `0` weakly in `⊕_(s in S) ℓ^1(X)`.
3. The set `{(f.s - f)_s : f a finitely supported probability}` is convex.
   By Mazur, its weak and norm closures agree. So for every `eta > 0` there is
   a finitely supported probability `f >= 0` with
   `sum_s ||f.s - f||_1 < eta`.
4. Layer cake. Put `F_t = {f > t}`. For reals `a, b >= 0`,
   `|a - b| = ∫_0^∞ |1{a > t} - 1{b > t}| dt`. Since `{f.s > t} = F_t s`,
   this gives
   `||f.s - f||_1 = ∫_0^∞ |F_t s Δ F_t| dt` and `∫_0^∞ |F_t| dt = ||f||_1 = 1`.
5. So `∫_0^∞ ( sum_s |F_t s Δ F_t| - eta |F_t| ) dt < 0`. The integrand is
   `0` when `F_t` is empty, so some `t` has `F_t` finite, nonempty and
   `sum_s |F_t s Δ F_t| < eta |F_t|`.
6. Put `F = F_t`. The arcs of `∂F` with label `s` are counted by
   `|F \ F s^(-1)| <= |F s^(-1) Δ F|`. Summing over `s` and using `S = S^(-1)`,
   `|∂F| <= sum_s |F s Δ F| < eta |F|`. Take `eta = epsilon`. `QED`

## Step 1. Reduction

* `p_c(G) <= p_c(I;G)`, since a cluster meeting `I` infinitely is infinite.
* `p_c(I;G) <= p_u(G)` by `fpbs-relative-gap-along-any-subgroup-separates`.
  So if `p_c(G) = p_u(G)` the equality holds.
* Otherwise `p_c(G) < p_u(G)`. By `fpbs-cluster-count-trichotomy`, for every
  `p in (p_c(G), p_u(G))` there are a.s. infinitely many infinite clusters.
* Let `A_I` be the event that some cluster meets `I` in infinitely many
  vertices. It is increasing, so `P_p(A_I)` is nondecreasing in `p`.
* **Zero-one law.** `A_I` is invariant under left multiplication by every
  `i in I`, since `iI = I` and `i` maps clusters to clusters. `I` is infinite
  and acts freely on vertices, so for a finite edge set `E_0` only finitely
  many `i` have `i E_0 ∩ E_0` nonempty. Approximating `A_I` by events on
  finitely many edges and using independence gives `P_p(A_I) = P_p(A_I)^2`.
* So it suffices to prove the following. For every `p in (p_c(G), p_u(G))`
  and every `p' > p`, `P_(p')(A_I) > 0`. Then `P_(p')(A_I) = 1` for all
  `p' > p_c(G)`, and `p_c(I;G) <= p_c(G)`.
* The statement `chi^I_p = infinity` for all `p > p_c(G)` then follows from
  the equivalence of conditions 1 and 2 in
  `fpbs-relative-gap-along-any-subgroup-separates`.

The proof of the reduced statement has two parts. Steps 2 to 4 show that at
`p`, some cluster meets some fibre infinitely. Step 5 moves this onto `I` by
sprinkling.

## Step 2. Trifurcations have positive, constant density

Fix `p in (p_c(G), p_u(G))`. Call `t` a **trifurcation** if `K(t) \ {t}` has
at least three infinite components, and let `T` be the set of trifurcations.

* `delta = P_p(o in T) > 0`. This is Step 1 of
  `fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof`. It uses
  only that there are infinitely many infinite clusters, finite energy on a
  ball `E(B_R)`, and invariance under left multiplication. It uses nothing
  about subgroups.
* `T` is defined from `omega` equivariantly under every automorphism. Left
  multiplication by `x` preserves Bernoulli percolation, so
  `P_p(x in T) = delta` for **every** vertex `x`. This is the only place the
  full group `Gamma` is used.

## Step 3. Cutting along the preimage of a Folner set

**Hypothesis H (for contradiction).** A.s., every cluster meets every fibre
of `pi` in finitely many vertices.

Fix `epsilon > 0` and `F` from Lemma 0. Put `W = pi^(-1)(F)`, a union of
`|F|` fibres. `W` is invariant under left multiplication by `I`.

* Let `xi` be the set of open edges with both endpoints in `W`. For `x in W`,
  let `C(x)` be the `xi`-cluster of `x`.
* **Finiteness.** `C(x) ⊆ K(x) ∩ W`, and `K(x) ∩ W` is the union of the `|F|`
  sets `K(x) ∩ pi^(-1)(phi)`, `phi in F`. Under H each is finite, so `C(x)` is
  finite.
* **Boundary.** Let `∂C` be the set of open edges with exactly one endpoint in
  `C`. An open edge at a vertex of `C` whose other endpoint is in `W` lies in
  `xi`, so it lies inside `C`. Hence every edge of `∂C` joins `C` to
  `Gamma \ W`. For `x in W` let `b(x)` be the number of open edges `{x, y}`
  with `y ∉ W`. Then `|∂C| = sum_(x in C) b(x)`.
* **Deterministic bound on `b`.** Pick one vertex `x_phi` in each fibre
  `pi^(-1)(phi)`, `phi in F`, and let `D = {x_phi}`, so `|D| = |F|`. The
  neighbours of `x` are the `xs`, `s in S`, and `pi(xs) = pi(x) s`. So
  `b(x_phi) <= #{s in S : phi s ∉ F}`. Summing,
  `sum_(x in D) b(x) <= |∂F| <= epsilon |F|`.
* **Counting lemma.** If `C` is a finite `xi`-cluster, then
  `|T ∩ C| <= |∂C|`. This is Step 4 of
  `fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof`, applied
  verbatim. That step uses only that `C` is a finite connected subset of an
  open cluster `K` and that `∂C` is its open edge boundary. It does not use
  how `C` was cut out.

## Step 4. Mass transport along the free action of I

**Lemma 4 (transport over a free action).** Let `f(x,y) >= 0` be a random
function on `W x W` whose law is invariant under the diagonal left action of
`I`. Then

```text
sum_(x in D) E sum_(y in W) f(x,y)  =  sum_(y in D) E sum_(x in W) f(x,y).
```

*Proof.*
1. Every `y in W` is `i y'` for a unique `y' in D` and a unique `i in I`,
   because `I` acts freely and `D` meets each `I`-orbit in `W` once.
2. By invariance, `E f(x, i y') = E f(i^(-1) x, y')`. So the left side is
   `sum_(x in D) sum_(y' in D) sum_(i in I) E f(i^(-1) x, y')`.
3. As `x` runs over `D` and `i` over `I`, `i^(-1) x` runs over `W` once each.
   All terms are nonnegative, so Tonelli gives the right side. `QED`

The pair `(omega, W)` is invariant under left multiplication by `I`, since the
law of `omega` is and `W` is a fixed `I`-invariant set. `T`, `xi`, `C` and `b`
are defined equivariantly. So Lemma 4 applies to both functions below.

* `f(x,y) = 1{x in T} 1{y in C(x)} / |C(x)|`. It is well defined under H.
  * The left side is `sum_(x in D) P(x in T) = delta |F|`, by Step 2.
  * `y in C(x)` iff `x in C(y)`, and then `|C(x)| = |C(y)|`. So the right side
    is `sum_(y in D) E[ |T ∩ C(y)| / |C(y)| ]`.
  * By the counting lemma this is at most
    `sum_(y in D) E[ |∂C(y)| / |C(y)| ]`.
* `g(x,y) = 1{y in C(x)} b(x) / |C(x)|`.
  * The left side is `sum_(x in D) E b(x) <= epsilon |F|`, by Step 3.
  * The right side is
    `sum_(y in D) E[ sum_(x in C(y)) b(x) / |C(y)| ] = sum_(y in D) E[ |∂C(y)| / |C(y)| ]`.

Combining,

```text
delta |F|  <=  sum_(y in D) E[ |∂C(y)| / |C(y)| ]  =  sum_(x in D) E b(x)  <=  epsilon |F| .
```

So `delta <= epsilon`. Since `epsilon` was arbitrary and `delta > 0` by
Step 2, this is a contradiction. **So H fails:** with positive probability
some cluster meets some fibre `Ix` in infinitely many vertices.

## Step 5. Sprinkling from a nearby fibre onto I

There are countably many fibres, so there is `x in Gamma` with
`P_p(E_x) > 0`, where `E_x` is the event that some cluster meets `Ix` in
infinitely many vertices. Put `r = |x|_S` and fix a path `gamma` of length `r`
in `G` from `x` to `o`. For `i in I`, the left translate `i gamma` is a path
of length `r` from `ix` to `i`, contained in the ball of radius `r` about `i`.

* Let `p' > p`, and let `eta` be Bernoulli(`q`) with `q = (p'-p)/(1-p)`,
  independent of `omega`. Then `omega' = omega ∨ eta` is Bernoulli(`p'`).
* On `E_x`, choose by a fixed rule a cluster `K` and an infinite set
  `J ⊆ I` such that:
  * `ix in K` for all `i in J`;
  * `d(i, j) > 2r + 1` for distinct `i, j in J`.

  For example, take the least index in a fixed enumeration, then choose
  greedily. This is possible because `K ∩ Ix` is infinite and balls are
  finite. The paths `i gamma`, `i in J`, are then pairwise edge-disjoint, and
  `J` is a function of `omega`.
* Conditionally on `omega`, the events `{eta opens every edge of i gamma}`,
  `i in J`, are independent, each of probability `q^r > 0`. By the second
  Borel--Cantelli lemma, infinitely many occur a.s.
* Each occurrence joins `ix in K` to `i in I` by an `omega'`-open path, and
  `K` lies in one `omega'`-cluster `K'`. So `K'` contains infinitely many
  vertices of `I`.

Hence `P_(p')(A_I) >= P_p(E_x) > 0`. With the zero-one law of Step 1 this
gives `P_(p')(A_I) = 1` for every `p' > p`, and `p` was any point of
`(p_c(G), p_u(G))`. So `p_c(I;G) <= p_c(G)`. `QED`

## Remarks

* **Why normality is not needed.**
  * The normal-subgroup proof built `Gamma`-invariant random cells on the
    quotient group, so that the mass-transport principle of the whole of
    `Gamma` applied.
  * Here transport runs only along the free `I`-action, whose orbits are
    exactly the fibres. A deterministic union of fibres is automatically
    `I`-invariant, so the Folner set can be fixed.
  * The equivariant random partition of the coset space, which that proof
    named as the missing object, is never needed. The only global input is
    that the trifurcation density is the same at every vertex.
* **Normal case.** For normal `N` the right cosets are the elements of
  `Gamma/N`, and co-amenability is amenability of `Gamma/N`. So this proof
  reproves `fpbs-amenable-quotient-normal-relative-threshold-is-pc`.
* **Sharpness of the method.** Lemma 0 is the only use of co-amenability. If
  `I` is not co-amenable, then `h = inf |∂F|/|F| > 0` by
  `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap` (a), and Step 4
  gives only `delta <= h`, which is no contradiction. That is exactly where the
  conjectured gap `fpbs-percolation-schreier-kesten-gap` would live. A proof of
  that gap therefore has to beat the bound `delta <= h(Sch(I\Gamma,S))`
  quantitatively; trifurcation counting over Schreier Folner fibres alone
  cannot give it.
