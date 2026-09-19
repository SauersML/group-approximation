---
rg: 2
id: deligne-third-floor-no-character-certificate-proof
kind: route
title: Pass to the profinite cochain space, identify its integral characters with finite leafwise cycles, and kill them with the identity-among-relations argument
target: deligne-third-floor-has-no-character-certificate
requires: [finitely-generated-linear-groups-are-residually-finite, deligne-opnorm-monomial-models-are-almost-flat-circle-bundles]
---

Notation of the target. `mu(X) = mu_(1/3)(X) = inf_a max_(x,r) dist((delta a)(x,r) - k_r/3, Z)`, as in
`deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`. Textbook facts used without citation: the Riesz
representation `C(K)* = M(K)` (finite signed regular Borel measures) for compact metrizable `K`; continuous
functions from a profinite space to `Z` are locally constant; Hurewicz for the simply connected `Y~`.

## Step 0: the lamination

`Gamma` is finitely generated and linear, hence residually finite
(`finitely-generated-linear-groups-are-residually-finite`). So `Gamma -> G` is injective and left multiplication
is a free continuous action on `G`.

Define the 2-complex-valued cochains exactly as for `Y_X`, with `X` replaced by `G`:
`(delta a)(x, r)` is the signed sum of `a` along the loop reading `r` from `x in G`. Here `a` is a function on edges
`(x, s)`, `x in G`, continuous in `x`. So `delta : C^1(Y; C(G,R)) -> E` is a bounded linear map, and
`||delta|| <= max_r |r|`.

For a finite-index normal `N`, the finite quotient `X_N = G / cl(N) = Gamma / N` is a `Gamma`-set. Pullback along
`G -> X_N` identifies `C^i(Y_(X_N); R)` isometrically with the cochains in `C^i(Y; C(G,R))` that are constant on
`cl(N)`-cosets. It commutes with `delta`, and it sends `k` to the constant cochain `k`.

## Step 1: the distance formula (item 1)

Write `L_N = C^2(Y_(X_N); Z) + delta C^1(Y_(X_N); R)`, viewed inside `E`. By the definition of `mu`,
`mu(X_N) = dist(k/3, L_N)` in the sup norm.

- **Monotonicity.** For transitive `X = Gamma/Lambda`, let `N` be the normal core of `Lambda`. Then `Gamma/N -> X`
  is a `Gamma`-map, so pulling back models gives `mu(X_N) <= mu(X)`. Hence `floor = inf_N mu(X_N)`.
- **Union.** `L_N` increases as `N` decreases, so `floor = dist(k/3, L_infty)`, where `L_infty = union_N L_N`.
- **Comparison with `L`.**
  - `L_infty ⊂ L`. So `dist(k/3, L) <= floor`.
  - Conversely, `C(G, Z) = union_N (functions constant on cl(N)-cosets)`, since continuous `Z`-valued functions
    on a profinite space are locally constant, and the `cl(N)`-cosets form a base of clopens.
  - Locally constant real functions are dense in `C(G, R)`, and `delta` is bounded. So `delta C^1(Y; C(G,R))`
    lies in the closure of `union_N delta C^1(Y_(X_N); R)`.
  - Hence `L ⊂ cl(L_infty)`, and `dist(k/3, L) >= dist(k/3, L_infty) = floor`.

So `floor = dist(k/3, L) = dist(k/3, cl L)`, and `floor > 0` iff `k/3 notin cl L`. ∎(1)

## Step 2: characters of `E` trivial on `L`

Let `chi : E -> T = R/Z` be a continuous homomorphism. `E` is a real Banach space, so it is simply connected and
`chi` lifts to a continuous additive `f : E -> R`. Such an `f` is `Q`-linear, hence `R`-linear by continuity. So
`chi = f mod Z` with `f in E*`. By Riesz, `f = (m_c)_c` is a finite family of measures `m_c in M(G)`, one per
2-cell `c = r` of `Y`, with `f(v) = sum_c ∫ v(x, c) dm_c(x)`.

**(a) `chi` trivial on `delta C^1(R)`.** `f` is real-valued on the real subspace `delta C^1(Y; C(G,R))` and
integer-valued there, so it vanishes on it. So `delta* f = 0`, i.e. `f` is a measure-valued 2-cycle.

**(b) `chi` trivial on `C^2(Y; C(G,Z))`.** Then `m_c(U) in Z` for every clopen `U ⊂ G` (test against `1_U`
placed on the cell `c`).

**Lemma.** A finite signed measure `m` on a profinite space `G` with `m(U) in Z` for every clopen `U` is a finite
`Z`-combination of Dirac masses.

*Proof.*
- *Atoms.* For `x in G`, choose clopens `U_n` decreasing to `{x}`. By countable additivity,
  `m({x}) = lim m(U_n) in Z`. The total variation `|m|(G)` is finite and each atom has `|m({x})| >= 1`, so there are
  finitely many atoms. Let `m_a` be the atomic part. It is a finite `Z`-combination of Diracs, so `m' = m - m_a`
  also takes integer values on clopens, and `m'` has no atoms.
- *Non-atomic part.* For each `x`, `|m'|({x}) = 0` and `|m'|` is regular, so `x` has a clopen neighbourhood `U_x`
  with `|m'|(U_x) < 1/2`. By compactness finitely many cover `G`. Refine them to a finite clopen partition `P`. For
  a clopen `V ⊂ P_i`, `|m'(V)| < 1/2` and `m'(V) in Z`, so `m'(V) = 0`.
- Every clopen `W` is the disjoint union of the clopens `W ∩ P_i`, so `m'(W) = 0`. The clopens form an algebra
  generating the Borel sets, so `m' = 0`.

Hence `m = m_a`. ∎

So `f = sum n_(c,x) [c, x]` is a finite integral 2-chain on the cells `(c, x)`, `x in G`, with `delta* f = 0`.

## Step 3: each character is leafwise spherical, so `chi(k/3) = 1` (item 2)

- **Leaves.** The boundary of a cell `(r, x)` involves only edges `(y, s)` with `y in Gamma x`. So the cycle
  condition splits along `Gamma`-orbits: `f = sum_O f_O`, where `f_O` is supported on the cells over the orbit `O`,
  and each `f_O` is a cycle.
- **Each leaf is the Cayley complex.** Fix `x_0 in O`. Freeness makes `g -> g x_0` a bijection `Gamma -> O`, which
  identifies the cells over `O` with the cells of the Cayley complex `Y~`, compatibly with boundaries. So `f_O` is a
  finite integral 2-cycle on the simply connected `Y~`, i.e. an element of `H_2(Y~; Z) = pi_2(Y)` (Hurewicz).
- **`k` vanishes on it.** A finite integral 2-cycle on `Y~` is an identity among relations. The words `w_i` and
  signs `eps_i`, with multiplicity, satisfy `prod_i w_i r_i^(eps_i) w_i^(-1) = 1` in the free group `F(S)`, and
  `sum_i eps_i k_(r_i) = k(f_O)`. Map `F(S)` to `Gamma~` by the lifted generators. Each `r_i` maps to the central
  element `z^(k_(r_i))`, so the product maps to `z^(k(f_O))`. It is also the image of `1`. Since `z` has infinite
  order in `Gamma~` (setting of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`; this is (K1)
  there), `k(f_O) = 0`.
- **Conclusion.** `f(k/3) = (1/3) sum_(c,x) n_(c,x) k_c = (1/3) sum_O k(f_O) = 0`. So `chi(k/3) = 1`. ∎(2)

## Step 4: consequences stated in the target

- If `cl L` were dually closed, i.e. equal to `{v : chi(v) = 1 for all continuous chi trivial on L}`, then Step 3
  gives `k/3 in cl L`. Step 1 then gives `floor = 0`. The floor node `deligne-schreier-complexes-have-a-uniform-third-cellular-floor`
  then fails, and so does `deligne-triple-cover-exact-mf-radical`, by the implication recorded in the floor node.
- Conversely, if `floor > 0`, then `k/3 in L^perp-perp \ cl L` witnesses that `cl L` is not dually closed.
- **Linear certificates.** Any lower bound of the form `dist(v, cl L) >= dist(f(v), Z) / ||f||`, with `f in E*` and
  `f(L) ⊂ Z`, is a character bound. By Step 3 it gives `0` at `v = k/3`.
- **Leafwise exactness.** On each leaf, choose a set-theoretic section `sigma : Gamma -> Gamma~`. Then
  `beta(g, s) in Z` on the edge from `g` to `s g`, defined by `s~ sigma(g) = z^(beta(g,s)) sigma(s g)`, satisfies
  `delta beta = k` on `Y~`. Reading a relator `r` from `g` composes these to `r~ sigma(g) = z^((delta beta)(g,r)) sigma(g)`,
  and `r~ = z^(k_r)`. So
  `k/3 = delta(beta/3)` leafwise, with no integer correction. This is the concrete content of
  `k/3 in L^perp-perp`.
