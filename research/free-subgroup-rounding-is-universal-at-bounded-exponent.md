---
rg: 2
id: free-subgroup-rounding-is-universal-at-bounded-exponent
kind: claim
title: For groups of exponent m, SDP value 1-eps of a symmetric Galois game gives a subgroup acting freely on G/K with mu-mass 1 - C(m) eps log k
distinct_from:
  galois-games-round-through-free-subgroups: that proves free-subgroup rounding and the kernel version with a dimension-weighted cost; this asks whether the cost can always be made dimension-free at bounded exponent.
---

**OPEN.** Is there `C(m)` such that for every finite group `G` of exponent `m`,
every `K <= G`, and every symmetric conjugation-invariant `mu`,
`SDP Gal(G,K,mu) >= 1 - eps` implies a subgroup `H` acting freely on `G/K` with
`mu(G \ H) <= C(m) eps log k`?

A yes would mean symmetric quotient gap constructions over bounded-exponent
groups never beat the linear loss `Theta(eps log k)`. That loss is attained by
Khot--Vishnoi (`elementary-abelian-galois-games-round-with-linear-loss`), and
the constructions would then separate SDP from integral value only in the
regime `eps log k -> infinity`. A no would be an explicit group whose
large-dimensional representations carry SDP certificates that no free subgroup
matches: a genuinely non-abelian symmetric gap phenomenon.

## Attempts

* **Irreducible-kernel rounding**
  (`galois-games-round-through-free-subgroups`, part 3). This proves the bound
  with `C` replaced by `3 d_max/(1 - cos(2 pi/m))`. It dies on large
  irreducibles: a representation can have `lambda = 1 - O(eps)` while
  `rho(s) != I` for `mu`-almost every `s`.
* **Abelian groups.** Yes, with `C(m) = 3/(1 - cos(2 pi/m))`: all `d = 1`.
* **Extraspecial 2-groups, `K` the centre.** Admissibility puts weight `1/2`
  on the `2^n`-dimensional irreducible, whose `lambda` is `mu(e) - mu(z)`. So
  `SDP >= 1 - eps` forces `mu(e) >= 1 - 2 eps`, and `H = {e}` works. No
  counterexample there.
* **Point stabilizers (unbounded exponent, `S_N`).** For transposition noise
  and semiregular `K`, `H = Stab(1)` is free on `G/K` with
  `mu(G \ H) = O(eps)`, although kernel rounding is vacuous. This suggests that
  the right subgroups are stabilizers of structure fixed by the certificate
  vector, not kernels. The missing piece is a stability lemma: a unit vector
  with orthonormal `K`-translates that is almost invariant under `mu` should
  yield a subgroup of large `mu`-mass meeting no conjugate of `K`. No such lemma
  is known here.
