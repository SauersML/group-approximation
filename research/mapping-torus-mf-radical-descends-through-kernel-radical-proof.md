---
rg: 2
id: mapping-torus-mf-radical-descends-through-kernel-radical-proof
kind: route
title: Every corona representation kills the kernel radical, so the mapping torus radical is a pullback
target: mapping-torus-mf-radical-descends-through-kernel-radical
requires:
  - universal-mf-quotient
  - finite-outer-order-mapping-torus-is-virtually-product
  - mapping-torus-mf-radical-lies-in-finite-residual
---

Write `C = prod_n M_{k_n} / (+)_n M_{k_n}` for a norm corona, and `Hom_MF(H)`
for the set of homomorphisms `H -> U(C)` over all such coronas.  By definition

```text
Rad_MF(H) = intersection of ker(rho), rho in Hom_MF(H).
```

**(MD1).**  If `alpha in Aut(K)` and `rho in Hom_MF(K)`, then
`rho o alpha in Hom_MF(K)` and `ker(rho o alpha) = alpha^{-1}(ker rho)`.
So `alpha^{-1}` permutes the family of kernels, and `alpha(R) = R`.  Hence
`phi` induces `psi in Aut(Q)`.  The subgroup `R x {0}` is normal in `G`,
because conjugation by the generator of `Z` acts on `K x {0}` as `phi`.  The
map `(k,n) -> (kR,n)` is a surjection `G -> Q semidirectProduct_psi Z` with
kernel `R x {0}`.

**(MD2).**  Let `rho in Hom_MF(G)`.  Its restriction to `K x {0}` lies in
`Hom_MF(K)`, so it kills `R x {0}`.  Thus `R x {0} <= ker rho` for every
`rho`, and `R x {0} <= Rad_MF(G)`.  For the upper bound, `Z` is residually
finite, hence MF, so the exponent map `G -> Z` composed with a faithful
corona representation of `Z` lies in `Hom_MF(G)`; its kernel is `K x {0}`.

**(MD3).**  By (MD2), every `rho in Hom_MF(G)` factors uniquely as
`rho' o pi` with `rho' in Hom_MF(Q semidirectProduct_psi Z)`.  Conversely every
such `rho'` gives `rho' o pi in Hom_MF(G)`.  Since
`ker(rho' o pi) = pi^{-1}(ker rho')` and preimages commute with intersections,

```text
Rad_MF(G) = pi^{-1}( Rad_MF(Q semidirectProduct_psi Z) ).
```

**(MD4).**  `pi` is surjective, so `pi^{-1}(X) = pi^{-1}(Y)` iff `X = Y`.
Also `pi^{-1}(Q x {0}) = K x {0}`.

**(MD5).**  If `phi^m = Ad(k)`, then `psi^m = Ad(kR)`, so `[psi]` has finite
order in `Out(Q)`.  By `universal-mf-quotient`, `Q = K/Rad_MF(K)` is MF.  By
`finite-outer-order-mapping-torus-is-virtually-product`, the group
`Q semidirectProduct_psi Z` is MF, so its radical is trivial.  By (MD3),
`Rad_MF(G) = pi^{-1}(1) = R x {0}`.

**Dichotomy.**  Let `(G,K)` witness `torsion-free-sofic-exact-mf-radical-over-z`.
Since `G/K ~= Z` is free, `G = K semidirectProduct_phi Z` for some `phi`.
Suppose `(DI)` fails, so `Q != 1`.

1. *Kazhdan.*  Let `(S,eps)` be a Kazhdan pair for `K`.  A unitary
   representation `sigma` of `Q` gives `sigma o q` of `K`, where `q: K -> Q`
   is the quotient map.  It has the same invariant vectors, and a
   `(q(S),eps)`-invariant vector for `sigma` is `(S,eps)`-invariant for
   `sigma o q`.  So `(q(S),eps)` is a Kazhdan pair for `Q`.
2. *No finite quotients.*  By `mapping-torus-mf-radical-lies-in-finite-residual`,
   `K = Rad_MF(G) <= R_fin(K)`, so `K` has no nontrivial finite quotient.
   Neither does its quotient `Q`.
3. *Infinite outer order.*  If `[phi]` had finite outer order, (MD5) would give
   `K = R`, contrary to `Q != 1`.  If `[psi]` had finite outer order, then
   `Q semidirectProduct_psi Z` would be MF, as in (MD5), and (MD3) would again
   give `Rad_MF(G) = R`.
4. *Exact radical.*  This is (MD4).

The two cases are exclusive, since `(DX)` requires `Q != 1`.

**Forced degree.**  If `L <= G` is Kazhdan, then by item 1 its image in `Z` is
Kazhdan.  That image is `0` or `mZ ~= Z`.  But `Z` is not Kazhdan: in `l^2(Z)`
the unit vectors `n^{-1/2} 1_{[0,n)}` move by the generator at most `(2/n)^{1/2}`,
and there is no nonzero invariant vector.  So `L <= K x {0}`.
