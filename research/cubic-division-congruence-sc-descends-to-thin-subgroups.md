---
rg: 2
id: cubic-division-congruence-sc-descends-to-thin-subgroups
kind: claim
title: Congruence strong convergence for SL_1(O_D) forces asymptotically Ramanujan congruence Cayley graphs for every thin free subgroup
distinct_from:
  sln-z-thin-codense-tau-pair: that uses a thin free subgroup of SL_n(Z) for co-density and property tau (a uniform gap); this transfers the sharp regular-norm limit, not a gap, from a cocompact division-algebra lattice to its thin subgroups.
---

ESTABLISHED (unreviewed).  Let `D`, `Gamma_D = SL_1(O_D)` and
`pi_p = l^2_0(SL_3(F_p))` be as in
`cubic-division-congruence-representations-converge-strongly`.  Let
`H <= Gamma_D` be finitely generated and nonamenable, and put
`H(p) = H cap Gamma_D(p)`.

1. For all primes `p` outside a finite set `P_H`, reduction `H -> SL_3(F_p)` is
   onto and `pi_p|_H = l^2_0(H / H(p))`.
2. If `pi_p -> lambda_(Gamma_D)` strongly, then
   `l^2_0(H / H(p)) -> lambda_H` strongly as `p -> infinity`, `p` not in `P_H`.
3. For a free subgroup `H = <a, b>` (Tits alternative), 2 says that the
   4-regular Cayley graphs `Cay(SL_3(F_p), {a, a^-1, b, b^-1} mod p)` have
   largest nontrivial absolute eigenvalue tending to `2 sqrt 3`.  More
   generally every element of `C[F_2]` has asymptotically regular norm.  This
   would be an explicit deterministic strongly convergent sequence for a free
   group, which van Handel's survey (arXiv:2510.12520, Section 2.2) records
   as open.  A uniform spectral gap for these graphs is already known
   (Salehi Golsefidy--Varju, expansion in perfect groups, GAFA 22 (2012);
   import, not re-read here).  The sharp constant is the new content.

**Contrapositive (the negative attack).**  If some finitely generated
nonamenable `H <= Gamma_D` and some `z in C[H]` satisfy
`limsup_p ||l^2_0(H/H(p))(z)|| > ||lambda_H(z)||`, then
`cubic-division-congruence-representations-converge-strongly` fails for this
`D`.  For free `H` and `z = a + a^-1 + b + b^-1`, one family of congruence
Cayley graphs with outliers above `2 sqrt 3` suffices.  The outlier may be
sought in any summand of `l^2_0(SL_3(F_p))`, for example
`l^2_0(P^2(F_p))`.

Proof: `cubic-division-congruence-sc-descends-to-thin-subgroups-proof`.
