---
rg: 2
id: k1222-planar-cover-fold-divisible-by-six
kind: claim
title: Every finite planar cover of K_{1,2,2,2} has fold divisible by 6, hence at least 18, because the Z_3 incidence phase of K_{1,2,2,2} has order 3
artifacts:
  - experiments/odd-p-incidence-pquotient-2026-09-17/run_k1222.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/run_k1222_cert.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_cert.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_p3_monomial.json.gz
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_verify.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/monomial_fast.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_p5.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_m4.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/k1222_m9.out
  - experiments/odd-p-incidence-pquotient-2026-09-17/verify_monomial.py
  - experiments/odd-p-incidence-pquotient-2026-09-17/pq.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/reduce.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/monomial.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/RESULTS.md
distinct_from:
  z3-heawood-incidence-system-has-a-finite-dimensional-solution: that certifies the Heawood graph and other cubic girth-six graphs, where Negami's conjecture is already known; this certifies K_{1,2,2,2}, the one graph on which Negami's conjecture is still open, and turns the certificate into a constraint on planar covers.
  slofstra-zhang-high-girth-phase-survival: Slofstra-Zhang Theorem 1.3 needs (min degree, girth) at least (4,4) or (3,6); K_{1,2,2,2} has girth 3, so it does not apply, and |J| in Gamma_3(K_{1,2,2,2}) was not known.
  lcs-phase-dies-in-every-nilpotent-quotient-of-class-below-p: that shows class p is the least class that can carry a certificate; here class 3 is attained for K_{1,2,2,2} at p=3.
---

**ESTABLISHED (exact computer certificate plus a written covering argument).**

Let `K = K_{1,2,2,2}`: vertices `1..7`, apex `1`, parts `{2,3},{4,5},{6,7}`,
and an edge between any two vertices in different parts (18 edges).  Orient
each edge from its smaller to its larger endpoint.  Let `b = delta_1`.  Write
`Gamma_m(G,b)` for the solution group of the oriented incidence system
`I(G)x=b` over `Z_m`:

- generators `x_e` for the edges and a central `J`;
- `x_e^m = J^m = 1`;
- `x_e x_f = x_f x_e` whenever `e` and `f` share a vertex;
- `prod_{e at v} x_e^{sigma(v,e)} = J^{b_v}`, with `sigma = +1` at the head
  and `-1` at the tail.

A *k-fold cover* `phi: H -> G` is a surjective graph homomorphism that maps
the edges at every vertex `v'` bijectively onto the edges at `phi(v')`, with
`|phi^{-1}(v)| = k` for every `v`.

**Claim.**

1. `J` has order exactly `3` in `Gamma_3(K, delta_1)`.  An explicit
   certificate: `3^8 x 3^8` monomial unitary matrices with cube-root-of-unity
   entries satisfy every defining relation, with `J = zeta_3 I`.  They factor
   through a 3-group of order `3^19`, nilpotency class 3, exponent 9 and
   centre `<J>`.
2. (Covering lemma; Slofstra-Zhang, arXiv 2412.10305, Lemma 3.10.)  If a
   connected graph `G` has a planar k-fold cover, then `J^{k|b|} = 1` in
   `Gamma_m(G,b)` for every `m`, where `|b| = sum_v b_v`.
3. Consequently every finite planar cover of `K_{1,2,2,2}` has fold divisible
   by `3`.
4. Combined with Archdeacon-Richter (a planar cover of a nonplanar graph has
   even fold) and Annor-Nikolayevsky-Payne (arXiv 2311.01672: `K_{1,2,2,2}`
   has no planar cover of fold below 14), every planar cover of `K_{1,2,2,2}`
   has fold in `{18, 24, 30, ...}`.  Folds 14 and 16 are newly excluded.

Items 1-3 turn Negami's planar cover conjecture into an order question about
`J` in solution groups.  If `J != 1` in `Gamma_p(K_{1,2,2,2}, delta_1)` for
infinitely many primes `p`, then `K_{1,2,2,2}` has no finite planar cover, and
by Hlineny's reduction Negami's conjecture follows.  The same lemma at `m=2`,
together with Arkhipov's theorem (`J != 1` in `Gamma_2(G)` iff `G` is
nonplanar), gives the Archdeacon-Richter parity theorem again.

Proof in `k1222-planar-cover-fold-divisible-by-six-proof`.  Reproduce the
certificate with `gunzip -k k1222_p3_monomial.json.gz; python3
verify_monomial.py k1222_p3_monomial.json k1222 3`.

## Attempts

- `p=5`: `J` dies in the 5-quotients of class `<= 4` (orders `5^12, 5^32,
  5^108, 5^384`).  This is forced by the Lazard bound (class `< p`).  Class 5
  is the first informative class; it did not finish within 1200 s.
- `m=4` (2-quotients): `J` has order 2, not 4, through class 4 (`2^473`); class 5 timed out.
- `m=9` (3-quotients): `J` has order 3, not 9, through class 4 (`3^493`); class 5 timed out.
