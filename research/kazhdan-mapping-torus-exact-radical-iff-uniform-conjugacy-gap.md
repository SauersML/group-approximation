---
rg: 2
id: kazhdan-mapping-torus-exact-radical-iff-uniform-conjugacy-gap
kind: claim
title: A Kazhdan mapping torus has exact MF radical iff the automorphism has a uniform operator-norm conjugacy gap on nontrivial corona representations, iff it is matricially stable
distinct_from:
  mf-kazhdan-quotientless-mapping-torus-exact-radical: That is the existence problem (XMF); this is an equivalence valid for every pair (K,phi), which turns (XMF) into a uniform chain-transience problem and shows every witness is matricially stable.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: That kills certificates valid in stably finite targets by a trace-1/N wrap; this characterizes the exact radical by the operator-norm wrap, so it says exactly what a surviving norm certificate has to prove.
  map-matricial-stability-non-mf: That assumes stability and minimal almost periodicity to get non-MF; this proves the converse direction for mapping tori, that the exact radical forces matricial stability.
  matricial-stability-identifies-radicals: That proves stability implies Rad_MF = Rad_fd for every group; this proves that for a mapping torus of a quotientless finitely generated group the exact radical implies stability, so the two are equivalent there.
  finitely-presented-full-radical-uniform-relator-gap: That is the uniform relator gap for a full radical Rad_MF(G) = G; this is the gap for a radical of index Z, where the stable letter is left free and only the kernel generators are forced near 1.
  quotient-permuting-and-ambient-inner-mapping-tori-are-lef: That kills automorphisms with a power inner in a LEF overgroup; clause (K1) here kills any power that is exactly or approximately inner on one nontrivial corona representation, with no LEF hypothesis.
  mapping-torus-mf-radical-lies-in-finite-residual: That bounds the radical by the finite residual; this is used as an input and adds the analytic equivalences.
  fournier-facio-group-matricially-stable: That derives stability from full asymptotic triviality of one group; this derives stability from asymptotic triviality on a kernel of index Z for every exact-radical mapping torus.
---

**ESTABLISHED.**  Proof: `kazhdan-mapping-torus-uniform-conjugacy-gap-proof`.

## Setting

- `K` is a countable group with property (T), and `(S,kappa)` is a Kazhdan
  pair for `K` with `S` finite and generating.
- `phi` is an automorphism of `K`, and `G = K semidirectProduct_phi Z`.  Write
  `t` for the stable letter, so `t k t^-1 = phi(k)`.
- A *corona* is `C = prod_n M_{k_n} / (+)_n M_{k_n}` for some sequence of
  positive integers `k_n`.  Note that `M_p(C)` is again a corona, with
  dimensions `p k_n`.
- For homomorphisms `alpha, beta : K -> U(C)`, put

```text
d(alpha, beta) = inf over u in U(C) of  max over s in S of  || u alpha(s) u^* - beta(s) ||.
```

  This is symmetric: replace `u` by `u^*`.

## Theorem

The following are equivalent.

- **(a) Exact radical.**  `Rad_MF(G) = K x {0}`.
- **(b) Uniform conjugacy gap.**  There is `eps_0 > 0` such that
  `d(rho o phi, rho) >= eps_0` for every corona `C` and every nontrivial
  homomorphism `rho : K -> U(C)`.
- **(c) Uniform chain transience.**  There is `eps_0 > 0` such that no corona
  `C` carries a closed `eps_0`-pseudo-orbit of nontrivial representations.
  Such a pseudo-orbit would be homomorphisms `rho_0, ..., rho_{p-1} : K -> U(C)`,
  with `p >= 1`, satisfying `d(rho_i o phi, rho_{i+1 mod p}) < eps_0` for all
  `i`.
- **(d) Finitary gap, for `G` finitely presented.**  Fix a finite presentation
  `<S u {t} | R_G>` of `G`.  For every `theta > 0` there is `delta > 0` with the
  following property.  For every `k`, every map `sigma : S u {t} -> U(k)` with
  `||r(sigma) - 1|| < delta` for all `r in R_G` also satisfies
  `max_{s in S} ||sigma(s) - 1|| < theta`.

In (b) and (c) the same `eps_0` can be used.  Moreover:

- **(e) Matricial stability.**  Suppose `K` has no nontrivial finite quotient.
  Then (a) holds iff `G` is matricially stable in Dadarlat's point-norm sense
  (`dadarlat-matricial-stability-obstruction`).  The direction (a) implies
  stability needs neither (T) nor the quotient hypothesis.  The converse
  needs only that `K` is finitely generated and quotientless.
- **(f) Uniform outerness of all powers.**  Under (a), with `eps_0` from (c),
  `d(rho o phi^m, rho) >= eps_0` for every `m != 0` and every nontrivial
  corona representation `rho` of `K`.  The constant does not depend on `m`.
- **(g) Chains cannot cross the trivial representation.**  If
  `eps < kappa` and `d(rho o phi, rho') < eps`, then `rho` is trivial iff
  `rho'` is trivial.

## Consequences for the flagship

**Every witness is matricially stable.**  A witness `(G,K)` of
`torsion-free-sofic-exact-mf-radical-over-z` is a split mapping torus
`K semidirectProduct_phi Z`, because `G/K = Z`.  Here `K` is Kazhdan and
finitely generated, and it is quotientless by
`mapping-torus-mf-radical-lies-in-finite-residual`.  By (e), `G` is
matricially stable.  So the flagship is equivalent to the following:

> there is a finitely presented, torsion-free, sofic, point-norm matricially
> stable group `K semidirectProduct_phi Z`, where `K` is a nontrivial Kazhdan
> group with no nontrivial finite quotient.

This holds in both branches: IO-int, where (b) is vacuous, and IO-ext.

**What (XMF) becomes.**  Take `Q = K / Rad_MF(K)` in branch (DX) of
`mapping-torus-mf-radical-descends-through-kernel-radical`.  Then `Q` has
nontrivial corona representations, and (XMF) for `(Q,psi)` is exactly (c).
Say that `psi^*` acts on the nontrivial MF dual by `rho -> rho o psi`.  Then
(XMF) holds iff `psi^*` is uniformly chain transient, meaning it has no closed
`eps_0`-chain.  This is the operator-norm, noncommutative analogue of
Pimsner's criterion, which says `C(X) semidirectProduct Z` embeds in an AF
algebra iff every point is chain recurrent.

## What this kills (K1--K3)

**Invariant.**  The `eps`-chain recurrence of `phi^*` on nontrivial corona
representations of `K`, measured by `d`.

**Step where each member dies.**  At (c): one closed `eps`-chain for every
`eps > 0` gives a corona representation of `G` that is nontrivial on `K`.

- **(K1) Periodic and approximately periodic automorphisms.**  Suppose that
  for every `eps > 0` some `m != 0` and some nontrivial corona representation
  `rho` have `d(rho o phi^m, rho) < eps`.  Then (a) fails.
  - This covers `phi^m` agreeing on `K` with conjugation by an element `h` of
    any overgroup `H` that has a corona representation nontrivial on `K`, for
    example an MF overgroup.
  - That generalizes the LEF-overgroup kill of
    `quotient-permuting-and-ambient-inner-mapping-tori-are-lef`.
- **(K2) Precompact orbits.**  Suppose some nontrivial `rho` has a
  `phi^*`-orbit that is totally bounded for `d` at scale `eps_0`.  Then
  pigeonhole gives `a < b` with `d(rho o phi^a, rho o phi^b) < eps_0`.
  - This is (f) with `m = b - a`, for the nontrivial representation
    `rho o phi^a`.  So (a) fails.
  - In every witness, every orbit of a nontrivial corona representation is an
    infinite `eps_0`-separated set.  This holds uniformly over all coronas.
- **(K3) Periodization as a refutation tool is complete.**  Attempt 1 of (XMF)
  shows that its periodization closes only after uncontrolled recurrence
  times.  By (c), periodization succeeding at every scale `eps` is not merely
  sufficient to refute (XMF) for a pair `(Q,psi)`; it is equivalent to that
  refutation.
  - Pseudo-orbits of any length `p` and in any corona are allowed.
  - The wrap error is an operator-norm `eps` on one block of normalized trace
    `1/p`.  This is precisely the norm-accurate wrap that
    `kazhdan-mapping-tori-have-proper-stably-finite-radical` names as the
    only survivor.

**What survives.**  A proof of (XMF), or of the flagship through branch
IO-ext, must produce a uniform `eps_0`.  It must show that no nontrivial
corona representation of `Q`, in any corona, is `eps_0`-close in
operator-norm conjugacy class to its own `psi`-pullback.  It must show the
same for every closed chain of such representations.  The recipes of Attempts
3--5 would produce such a bound only indirectly: they prove (a), and (a)
implies (b).  Pimsner's commutative criterion is recorded at
`pimsner-cyclic-transformation-af-equivalence`.  Branch IO-int has no such condition, but
its witness is still matricially stable, by (e).
