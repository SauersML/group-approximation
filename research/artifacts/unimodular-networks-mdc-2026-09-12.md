# Unimodular integral networks and the measure-theoretic determinant conjecture

Date: 12 September 2026 (fork `determinant-unimodular-networks`). Written
proofs, no machine verification. Statements marked *read* were checked on
2026-09-12 against the arXiv TeX sources. Statements marked *standard* were not
re-derived here.

## 0. Sources and setting

**Lück--Sauer--Wegner**, arXiv:0903.2925, *L2-torsion, the measure-theoretic
determinant conjecture, and uniform measure equivalence*. *Read:*
- **Measured equivalence relation:** a countable Borel equivalence relation `R`
  on a standard probability space `(X, mu)` with `mu` invariant (they cite
  Feldman--Moore I, Section 2).
- **Integral groupoid ring** `ZR`: the `f in L^infinity(R, Z)` for which, for
  some `N`, almost every row `{y : f(x,y) != 0}` and column
  `{y : f(y,x) != 0}` has at most `N` elements.
  - Product: `(fg)(x,y) = sum_z f(x,z) g(z,y)`.
  - Involution: `f^*(x,y) = f(y,x)`.
  - Trace: `tr(f) = integral_X f(x,x) d mu`.
  - `N(R)` denotes the von Neumann algebra of `R`.
- **MDC:** `R` *satisfies MDC* if `det_N(R)(A) >= 1` for every
  `A in M_(m x n)(ZR)`, using the generalized Fuglede--Kadison determinant.
  **Conjecture:** every measured equivalence relation satisfies MDC.
- **Known cases** (their introductory theorem):
  - amenable groups satisfy MDC, meaning all their essentially free standard actions do;
  - MDC passes to subgroups, amenable extensions, quotients by finite normal subgroups, and directed colimits;
  - Bernoulli actions of residually amenable groups satisfy MDC.
- **Groups:** if `G` satisfies MDC, every group measure equivalent to `G`
  satisfies the determinant conjecture.

**Elek--Lippner**, arXiv:0906.3619, *Sofic equivalence relations*. *Read:*
- **Sofic relations** satisfy MDC (Theorem, Section "The Measurable Determinant Conjecture").
- **Sources of sofic relations:** the Bernoulli shift of a sofic group is sofic
  (Proposition), and treeable relations are sofic (Section "Treeable relations").
- **Embedding:** if `R` is sofic, `N(R)` embeds in `R^omega`.
- **Closing question:** does a nonsofic measured equivalence relation exist?

*Standard:*
- **(MT)** `mu` is `R`-invariant iff
  `integral sum_(y ~ x) F(x,y) d mu(x) = integral sum_(y ~ x) F(y,x) d mu(x)`
  for every Borel `F : R -> [0, infinity]` (Feldman--Moore).
- **(FC)** For self-adjoint `T` in a finite von Neumann algebra and a real
  polynomial `f`, `log det f(T) = integral_(f != 0) log|f| d mu_T`. Also
  `det(A) = det(A^* A)^(1/2)`.
- **(FK)** `det(XY) = det(X) det(Y)` for invertible `X, Y` (Fuglede--Kadison),
  and `0 <= S <= T` implies `det S <= det T`.

**Networks.** As in `serre-class-from-unimodular-integral-realizability`: a
connected locally finite graph with integer symmetric weights `w`, loops
allowed, and weighted degree `sum_v |w(u,v)| <= D`.
- **Unimodular:** `E sum_v f(G,o,v) = E sum_v f(G,v,o)` for every Borel
  `f >= 0` on doubly rooted networks (Aldous--Lyons).
- **Expected root measure:** `mu_net = E <E_A(.) delta_o, delta_o>`.
- **Edge convention:** we take the edges to be exactly the pairs with `w != 0`.
  This loses nothing: the root measure sees only the component of `o` in the
  support of `w`, and passing to that component keeps unimodularity (apply mass
  transport to `f` times the indicator that `v` lies in that component).

`S` is the Serre class of
`research/artifacts/determinant-conjecture-serre-class-2026-09-11.md`.

## 1. The network claim is the measure-theoretic determinant conjecture

**Theorem 1.**
1. Let `(G,o)` be a unimodular integral network. If the relation of its
   labeled version (1.1) satisfies MDC, then `mu_net in S`.
2. Let `R` be a measured equivalence relation. If every network built from `R`
   as in 1.2 has `mu_net in S`, then `R` satisfies MDC.

So `serre-class-from-unimodular-integral-realizability` holds if and only if
every measured equivalence relation satisfies MDC.

### 1.1 From networks to relations

Let `(G,o)` have law `P`.

1. **Labels.** Attach i.i.d. uniform `[0,1]` labels `l(v)`; call the labeled
   law `P'`. It is unimodular.
   - Given Borel `f >= 0` on doubly rooted labeled networks, the average
     `g(G,o,v) = E_l f(G,l,o,v)` is a Borel function of the doubly rooted
     network, because the label law is invariant under isomorphisms.
   - Tonelli and mass transport for `P` give
     `E' sum_v f(G,l,o,v) = E sum_v g(G,o,v) = E sum_v g(G,v,o) = E' sum_v f(G,l,v,o)`.
   - Almost surely the labels are distinct, so the labeled network has no
     nontrivial automorphism.
2. **The relation.** Let `X` be the Borel set of labeled rooted networks with
   distinct labels, and `R = {((G,l,o),(G,l,v)) : v in V(G)}`.
   - `v -> (G,l,v)` is injective because the labels are distinct, so each class
     is in bijection with `V(G)` and is countable.
   - `R` is the injective Borel image of the space of doubly rooted labeled
     networks, hence Borel (Lusin--Souslin).
3. **Invariance.** Doubly rooted labeled networks are exactly the pairs in `R`,
   so mass transport for `P'` is (MT). Hence `(X, R, P')` is a measured
   equivalence relation.
4. **The element.** Put `T(x,y) = w(o,v)` for `x = (G,l,o)` and
   `y = (G,l,v)`.
   - `T` is Borel and integer valued with `|T| <= D`, and each row and column
     has at most `D` nonzero entries. So `T in ZR` and `T^* = T`.
   - On `l^2` of a class, `T` is the adjacency operator of `G`, so
     `tr(T^k) = E (A^k)_(oo) = integral t^k d mu_net`.
   - Both measures live in `[-D, D]`, so `mu_T = mu_net`.
5. **Conclusion.** For nonzero `Q in Z[x]`, `Q(T)` is a self-adjoint element of
   `ZR`. MDC gives `det Q(T) >= 1`, and (FC) turns this into
   `integral_(Q != 0) log|Q| d mu_net >= 0`.

### 1.2 From relations to networks

Let `R` on `(X, mu)` be measured and `A in M_(m x n)(ZR)`.

1. **Reduction.** `B = A^* A in M_n(ZR)` is self-adjoint and
   `det A = det(B)^(1/2)`, so it suffices to show `log det B >= 0`.
2. **The network.** For `x in X` take the vertex set `[x] x {1..n}` and
   weights `w((y,i),(z,j)) = B_ij(y,z)`. Root at `(x,i)` with `x ~ mu` and `i`
   uniform, and keep the component of the root.
   - Discard a null invariant set so that the row bounds hold everywhere.
   - The weights are integers and symmetric (`B^* = B`), and the weighted
     degree is at most `n N max|B|`.
   - The rooted isomorphism class is a Borel function of `(x,i)`: enumerate
     the classes by a countable group (Feldman--Moore).
3. **Unimodularity.** Let `N_x` be the network on `[x] x {1..n}`, and let
   `f >= 0` be Borel on doubly rooted networks, vanishing off the root
   component. Put `F(x,y) = sum_(i,j) f(N_x, (x,i), (y,j))`.
   - `N_x = N_y` for `x ~ y`.
   - So `n E sum_v f(G,o,v) = integral sum_y F(x,y) d mu`
     and `n E sum_v f(G,v,o) = integral sum_y F(y,x) d mu`.
   - These agree by (MT).
4. **The measure.** On `l^2([x] x {1..n})` the adjacency operator is `B`
   acting along a class, so
   `E (A_net^k)_(oo) = (1/n) sum_i integral (B^k)_ii(x,x) d mu = (1/n) tr_n(B^k)`.
   So `mu_net` is the spectral measure of `B` for the normalized trace.
5. **Conclusion.** `mu_net in S` with `Q = x` gives
   `integral_(t != 0) log|t| d mu_B >= 0`, i.e. `log det B >= 0`. Normalizing
   the trace only rescales `log det`.

### 1.3 Consequences

- **Relation by relation.** A network violating a Serre inequality gives a
  measured relation violating MDC (1.1), and conversely (1.2). By Elek--Lippner
  that relation is not sofic.
- **Subrelations.**
  - If `S` is a subrelation of `R` on the same space, `ZS` sits in `ZR` with
    the same trace. Spectral measures are determined by trace moments, so MDC
    for `R` implies MDC for `S`.
  - So a violation by `A in M_n(ZR)` already occurs in the subrelation
    generated by the support of `A`, and that subrelation must be nonsofic.
- **Groups.**
  - For an essentially free action of `G`, each `g` gives an element of `ZR`
    with `tr(g) = mu(Fix g)`, which is `1` for `g = e` and `0` otherwise. So
    `Z[G]` embeds in `ZR` with the same trace.
  - MDC for `R` then gives the determinant conjecture for `G`. This is route
    `determinant-via-unimodular-integral-networks` in relation form; LSW prove
    the stronger measure-equivalence version.
- **Credit.** Theorem 1 combines standard facts: the Aldous--Lyons dictionary
  between unimodular networks and measured relations, LSW's definitions, and
  (FC). It is a dictionary, not a new theorem. What it shows is that the repo's
  open claim is a named conjecture from 2009, which implies the determinant
  conjecture for every group.

## 2. Unimodular averaging loses integrality

**Proposition 2.**
1. **Finite.** The two-vertex network with loops of weight `2` and `3`, one edge
   of weight `1`, and a uniform root is unimodular. Its determinant is `sqrt 5`
   and its first root moment is `N_1 = 5/2`.
2. **Infinite.** Let `p in (0,1)` and `g = (g_k)_(k in Z)` be i.i.d. with
   `P(g_k = 2) = p` and `P(g_k = 1) = 1-p`. Put `w(k,k) = 2 g_k^2` and
   `w(k,k+1) = w(k+1,k) = g_k g_(k+1)`. The resulting network on `Z` is
   connected, ergodic, integral, unimodular and sofic, with determinant `4^p`
   and `N_1 = 2(1+3p)`. At `p = 1/4` these are `sqrt 2` and `7/2`.

*Proof.*
1. `B = [[2,1],[1,3]]` has eigenvalues `(5 ± sqrt 5)/2` and determinant `5`. A
   finite network with a uniform root is unimodular, and `mu_net` is uniform on
   the two eigenvalues. So `log det = (1/2) log 5` and `N_1 = tr(B)/2 = 5/2`.
2. The law is translation invariant with an i.i.d. decoration, so the network
   is unimodular and ergodic. It is the Benjamini--Schramm limit of the same
   decoration on cycles, so it is sofic.
   - **Setting.** Let `R` be the orbit relation of the shift on `{1,2}^Z` with
     product measure. The action is essentially free, so
     `N(R) = L^infinity x| Z` contains `M_g` (multiplication by `g_0` along the
     orbit) and the shift `s`, and its trace restricts to the group trace on
     `L(Z)`. The operator is `T = M_g K M_g` with `K = 2 + s + s^(-1)`.
   - **`K`.** `det K = exp integral_0^1 log(2 + 2 cos 2 pi theta) d theta = exp(2 m(1+z)) = 1`,
     by Jensen's formula `m(1+z) = 0`.
   - **`M_g`.** `det M_g = exp E log g_0 = 2^p`.
   - **Squeeze.** For `eps > 0`, (FK) gives
     `det(M_g (K + eps) M_g) = 4^p det(K + eps)`.
     - `K` is injective, so `det(K + eps)` decreases to `det K = 1` by monotone
       convergence.
     - `M_g (K + eps) M_g = T + eps M_g^2` lies between `T + eps` and
       `T + 4 eps`.
     - `T` is injective, so both bounds have determinant tending to `det T`.
     - Hence `det T = 4^p`.
   - **Moment.** `N_1 = E w(0,0) = 2 E g_0^2 = 2((1-p) + 4p) = 2(1+3p)`.

**Consequences.**
- **No integer-valued Fuglede--Kadison-type determinant.**
  - A determinant that agrees with Fuglede--Kadison on sofic integral networks
    takes the value `sqrt 5`, and also `4^p` for every `p in (0,1)`, which
    covers `(1,4)`.
  - Part 2 has no vertex count to normalize away: the network is infinite and
    ergodic.
  - What can hold is the bound `det >= 1`, and by Theorem 1 that bound is MDC.
- **No integer necklace numbers.**
  - The necklace numbers `p_k = (1/k) sum_(d | k) mobius(k/d) N_d` begin with
    `p_1 = N_1`, which is `5/2` or `7/2` here.
  - For a group ring, the trace `tau(a) = a(e)` is an integer coefficient. That
    is where `torsion-free-integral-zeta-is-an-integer-euler-product` gets its
    integers.
  - In `ZR`, `tr(chi_E) = mu(E)` takes every value in `[0,1]`. Mass transport
    equates two averages over roots and never forces an average to be an
    integer.
- **Not a counterexample.** Both networks are sofic and obey every Serre
  inequality. Integrality is what gets lost, not the inequality.

## 3. Where a violation can live

- **Nonsofic relations only.** By Theorem 1 and Elek--Lippner, a violating
  network has a nonsofic labeled relation. So it is not treeable, not a
  Bernoulli shift of a sofic group, and not the orbit relation of an essentially
  free action of a group satisfying MDC. Amenable groups, and everything LSW
  build from them by subgroups, amenable extensions, finite quotients and
  colimits, are excluded.
- **Nonsofic relations exist on main.**
  - `non-ce-property-t-equivalence-relation-exists` records an ergodic
    property (T) measured relation whose `N(R)` is not Connes embeddable. By
    Elek--Lippner's embedding theorem it is not sofic, which answers their
    closing question inside the graph.
  - MDC for that relation is open. The relation is built as a property (T)
    envelope of a non-co-hyperlinear IRS, and no element of its groupoid ring
    has a computable spectral measure.
- **Aldous--Lyons counterexamples.** The nonsofic unimodular networks of
  Bowen--Chapman--Lubotzky--Vidick are not explicit either. No candidate
  element with a computable root measure was found.

## 4. Status for the lane

- **Integer-valued determinant for unimodular networks:** does not exist
  (Proposition 2). Settled negatively.
- **`det >= 1` for all unimodular integral networks:** this is MDC (Theorem 1),
  and it implies the determinant conjecture for every group. Not proved.
- **Nonsofic counterexample:** not found. It must be a nonsofic relation, and
  the nonsofic relations known on main are not explicit.
