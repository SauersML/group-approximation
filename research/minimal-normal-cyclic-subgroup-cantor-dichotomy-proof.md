---
rg: 2
id: minimal-normal-cyclic-subgroup-cantor-dichotomy-proof
kind: route
title: Kakutani-Rokhlin tower sums make the type semigroup of the minimal cyclic subgroup a simple dimension group, and the coinvariant lemma runs on the quotient group
target: minimal-normal-cyclic-subgroup-cantor-dichotomy
requires: [coinvariant-tarski-lemma-minimal-nowhere-scattered, rainone-type-semigroup-crossed-product-dichotomy]
---

Let `T` generate `H`, and write `(t f)(x) = f(t^(-1) x)`, so moving a clopen
piece `C` by `t` turns `1_C` into `t 1_C = 1_(tC)`.

**Step 1: `S(X, H)` is the positive cone of a simple dimension group.**
Take nested Kakutani--Rokhlin partitions `P_n` for `T` (Herman--Putnam--Skau
1992).  Their bases `B_n` decrease to a point `x_0`, and their levels generate
the topology.  A tower `tau` of `P_n` has base `C_tau` and levels `T^j C_tau`
for `0 <= j < J_tau`, and `T^(J_tau) C_tau subset B_n`.  For `f in C(X, Z)`
constant on the levels of `P_n`, put `sigma_n(f)_tau = sum_j f(T^j C_tau)`.

* *Equal tower sums give equidecomposability.*  If `f, g in C(X, N)` are
  `P_n`-measurable and `sigma_n(f) = sigma_n(g)`, move the `f(T^j C_tau)`
  copies of level `j` by `T^(-j)` onto the base.  This gives
  `f ~ sum_tau s_tau 1_(C_tau) ~ g`.
* *Equidecomposability gives equal tower sums.*  If `f ~ g` with pieces `c_i`
  moved by `T^(k_i)`, then `f - g = h - T h` for the continuous function
  `h = sum_i sum_(0 <= j < k_i) T^j c_i` (use `-j` for negative `k_i`).
  * For large `n`, `f`, `g` and `h` are `P_n`-measurable, and `h` is constant
    on `T^(-1) B_n`.
  * Along a tower, `sum_j (h - T h)(T^j c) = h(T^(J-1) c) - h(T^(-1) c) = 0`,
    because both points lie in `T^(-1) B_n`.
  * So `sigma_n(f) = sigma_n(g)`.

Hence `S(X, H)` is the direct limit of the monoids `N^(towers of P_n)` under
the positive maps recording how towers of `P_(n+1)` run through towers of
`P_n`.  Every nonnegative vector is `sigma_n` of a function supported on the
bases.  So `S(X, H)` is cancellative, and it is the positive cone of the
simplicial limit `lim Z^(towers of P_n)`.  That limit is a dimension group,
and it equals `K^0(X, H)`, since coboundaries have eventually zero tower sums.
It is simple: by minimality, finitely many `T`-translates of a nonempty clopen
set cover `X`, so every nonzero positive class dominates `[1]`.  It is
noncyclic.  An invariant probability measure `mu` exists (`H` is amenable),
tower heights tend to infinity since `X` is infinite and `T` is minimal, so
`mu(B_n) -> 0` while `[1_(B_n)] != 0`.  A cyclic simple dimension group would
bound `mu` below on nonzero classes.

**Step 2: coinvariants in stages.**
* Since `H` is normal, `gamma (h - T h) = gamma h - (gamma T gamma^(-1)) gamma h`
  is again an `H`-coboundary.  So `Gamma` acts on `K^0(X, H)` by order
  automorphisms, and `H` acts trivially.
* Suppose `[f]_H = sum_i u_i` and `[g]_H = sum_i gamma_i u_i` in `K^0(X, H)^+`.
  Lift `u_i` to `f_i in C(X, N)`.  By cancellation, `f ~_H sum_i f_i` and
  `g ~_H sum_i gamma_i f_i`.  So `f ~_Gamma g`.
* The converse is clear.

So `S(X, Gamma)` is the type semigroup of `Gamma / H` acting on `K^0(X, H)`.

**Step 3: the lemma.**
* `K^0(X, H)` satisfies (R) and (P), being a dimension group.
* It satisfies (ND), being simple and noncyclic (model test in
  `coinvariant-tarski-lemma-minimal-nowhere-scattered-proof`).
* Every action on a simple group is minimal.

So infinite multiples are properly infinite.  A nontrivial state on
`S(X, Gamma)` is finite by simplicity.  It defines a finitely additive invariant
function on clopen sets, hence an invariant probability measure after
normalization (countable additivity by compactness).  Conversely a measure
gives a state.  With no state, Tarski and the lemma make `S(X, Gamma)` purely
infinite.

**Step 4: the crossed product.**
* `C(X)` is unital, separable, exact, has total projections and cancellation,
  and `K_0(C(X)) = C(X, Z)` has Riesz refinement.  Rainone identifies
  `S(C(X), Gamma, alpha)` with `S(X, Gamma)` (page 9).
* The action is minimal because `H` is.  For commutative coefficients,
  topological freeness means that each `alpha_t` with `t != e` is properly
  outer.
* The crossed product is simple (Olesen--Pedersen, Theorem 7.2).
* With an invariant measure, the induced tracial state is faithful by
  minimality, and Theorem 4.13 (`(1) => (3)`) gives stable finiteness.
* Without one, `S(X, Gamma)` is purely infinite by Step 3, and Theorem 4.21
  (`(1) => (3)`) gives pure infiniteness.
* The two cases exclude each other.
