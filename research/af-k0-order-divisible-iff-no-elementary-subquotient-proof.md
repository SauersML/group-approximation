---
rg: 2
id: af-k0-order-divisible-iff-no-elementary-subquotient-proof
kind: route
title: Koenig's lemma on the Bratteli diagram of a corner turns the absence of finite-dimensional representations into uniformly large blocks, which divide with small remainders
target: af-k0-order-divisible-iff-no-elementary-subquotient
requires: []
---

Standard facts used for an AF algebra `A = D tensor K`:

* `K_0(D)^+` is the set of classes of projections in `A`, and `A` has
  cancellation.
* A hereditary subalgebra of an AF algebra is AF.
* A unital AF algebra is the closure of an increasing union of
  finite-dimensional subalgebras containing the unit.
* Projections lift along quotient maps between AF algebras.

**Compression.**  Let `p in A` be a projection and `B = pAp`.  If `a, b` are
projections in matrices over `B` and `v` is a partial isometry over `A` with
`v^* v = a` and `v v^* <= b`, then `v = b v a` has entries in `B`.  So
subequivalence between projections over `B` is the same in `B` and in `A`.
Moreover, if `N d <= c = [p]` in `K_0(D)`, then `d = [q]` for some `q <= p`, and
there are orthogonal `q_1, ..., q_N <= p` with `q_j ~ q`.  All the relevant
classes are then represented over `B`.

**2 => 1.**  Let `c = [p]` be nonzero and `N, M >= 1`.  Write `B = pAp` as the
closure of `B_1 subset B_2 subset ...`, finite-dimensional with `1_B in B_1`.
Put `K_0 = N M`.

*Claim: some `B_m` has all matrix blocks of size at least `K_0`.*  Otherwise
every `B_m` has a block of size `< K_0`.

* If a block `b` of `B_(m+1)` is small, every block of `B_m` entering `b` with
  nonzero multiplicity is small.  At least one does, since `1_B in B_m`.
* By Koenig's lemma (finitely many blocks per stage), there is an infinite
  chain `b_1, b_2, ...` of small blocks, with `b_m` entering `b_(m+1)`.
* Sizes along the chain are nondecreasing and bounded.  So from some `m_0` on
  they equal a constant `k`, and `b_(m+1)` receives exactly one copy of `b_m`
  and nothing else.
* Hence, with `pi_m : B_m -> b_m` the block projection,
  `pi_(m+1) restricted to B_m = theta_m o pi_m` for a unital isomorphism
  `theta_m : b_m -> b_(m+1)`.
* The maps
  `rho_m = theta_(m_0)^(-1) o ... o theta_(m-1)^(-1) o pi_m : B_m -> M_k`
  are compatible for `m >= m_0`.  They extend to a unital representation
  `B -> M_k`, contradicting 2.

In a block of size `k >= NM` write `k = N a + r` with `0 <= r < N`.  Let
`q in B_m` have rank `a` in every block.  Then `N[q] <= [1_B]`, and the
remainder has rank `r` in each block with `M r < NM <= k`.  So
`M([1_B] - N[q]) <= [1_B]` in `K_0(B_m)`.  This holds in `K_0(B)` and then in
`K_0(D)`, so `d = [q]` works.

**1 => 2.**  Suppose `sigma : B = pAp -> M_k` is a nonzero finite-dimensional
representation.  Passing to an irreducible summand, `sigma` is irreducible, so
`sigma(1_B) = 1`.  Take `N = 2k`, `M = 2`, and suppose `d` works for `c = [p]`.

* By the compression paragraph, `d = [q]` and there are orthogonal
  `q_1, ..., q_N <= p` in `B` with `q_j ~ q` in `B`.
* Put `r = p - sum_j q_j`, so `[r] = c - N d`.
* `M(c - N d) <= c` gives `r direct_sum r <~ p` over `B`.
* Apply `sigma` and take ranks.  With `a = rank sigma(q)`: `2k a <= k` forces
  `a = 0`, so `rank sigma(r) = k`, and then `2k <= k`.  This is a contradiction.

**3 => 2.**  Suppose `sigma : B -> M_k` is irreducible.

* It extends to an irreducible representation `pi` of `A` on `H` with
  `pi(p)` of rank `k`.
* An irreducible C\*-algebra containing a nonzero compact operator contains
  `K(H)`.  So `J' = pi^(-1)(K(H))` and `I' = ker pi` satisfy
  `J'/I' isomorphic to K(H)`.
* Closed ideals of `A = D tensor K` have the form `I tensor K`.  So
  `J'/I' isomorphic to (J/I) tensor K` for ideals `I subset J` of `D`.
* `J/I` embeds as a hereditary subalgebra of `K(H)`, hence is elementary.
  This contradicts 3.

**2 => 3.**  Suppose `J/I isomorphic to K(H)`.

* Lift a rank-one projection `e in J/I` to a projection `p in J`.
* Since `J/I` is an ideal of `D/I`, we have `p (D/I) p subset J/I`.
* So the quotient map sends `pDp` into `e K(H) e = C e`, which is a
  one-dimensional representation of the corner `pDp subset p A p`.
* Every element of `pAp` compresses into `pDp` (identify `D` with
  `D tensor e_11`), so `pAp = pDp`, contradicting 2.
