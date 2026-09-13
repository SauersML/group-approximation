---
rg: 2
id: sl3z-satisfies-strong-atiyah
kind: claim
title: SL_3(Z) satisfies the Strong Atiyah Conjecture, with denominator 24
distinct_from:
  sl3z-strong-atiyah-denominators-divide-48: that is the established weaker bound with denominator 48; this is the conjectured sharp denominator 24.
  strong-atiyah-torsion-free: that is Strong Atiyah for torsion-free groups; SL_3(Z) has torsion, so this is the bounded-torsion form with denominator the lcm of finite subgroup orders.
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
---

**OPEN.** For every finite matrix `A` over `C[SL_3(Z)]`,
`24 * rk_{N(SL_3(Z))}(A) in Z`.

The finite subgroups of `SL_3(Z)` have orders dividing 24, and `S_4` occurs, so
24 is the Strong Atiyah denominator. Fisher--Ng (arXiv:2606.19606, Section 1,
read from source) say it "is not known whether `GL_m(Z)` satisfies" SAC. Only
Weak Atiyah is recorded, via a torsion-free finite-index subgroup. SAC for
`SL_3(Z)` gives SAC for `GL_3(Z) = SL_3(Z) x {+-I}`, whose lcm is 48.

Established so far:
- the denominator divides 48 (`sl3z-strong-atiyah-denominators-divide-48`);
- the claim is equivalent to Strong Atiyah with denominator 8 for the index-21
  discrete Iwahori subgroup `K_I = {g : g mod 2 upper unitriangular}`, whose
  ranks are already known to lie in `(1/16)Z`
  (`sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8`). So exactly one
  factor of 2 is missing.

## Attempts

1. **Congruence indices at odd primes.** Dead for the 2-part. For odd `p` the
   Sylow 2-subgroup of `SL_3(F_p)` has order divisible by 16. It lifts to
   `SL_3(Z_p)` and meets every torsion-free open subgroup trivially, so every
   such index has 2-adic valuation at least 4.
2. **A torsion-free open subgroup of `SL_3(Z_2)` of index 168.** Dead. The route
   `sl3z-strong-atiyah-via-iwahori-index-8` needed
   `sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8`, which is refuted by
   exhaustive search: `sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48`.
   For every prime `p`, every torsion-free open subgroup of `SL_3(Z_p)` has index
   divisible by 48. So restricting ranks to finite-index subgroups with a
   torsion-free `p`-adic closure, where Farkas--Linnell applies, can never beat
   denominator 48. That bound is already established. Reaching 24 needs a
   different idea: a subgroup satisfying Strong Atiyah that does not embed in a
   torsion-free `p`-adic analytic group through its closure, or the
   crossed-product argument below.
3. **Crossed product.** With `H = Gamma(3)`, `D(G) = D(H) * SL_3(F_3)` is
   semisimple Artinian. SAC is equivalent to every simple module having
   `D(H)`-dimension divisible by 234. Not attacked: nothing on main computes
   the `SL_3(F_3)`-action on `D(Gamma(3))`.
4. **Linnell--Schick, finite extensions** (arXiv:math/0403229, read from the
   PDF, 2026-09-12). Only Lemma 2.4 applies: SAC follows from SAC for the
   preimages of the Sylow subgroups of a finite quotient. Over `SL_3(Z/4)` it
   gives the reduction to `K_I` above. The other criteria are blocked.
   - **Elementary amenable quotients.** Theorem 1.6, Proposition 2.6 and
     Corollary 2.7 need a quotient `G -> A` with `A` elementary amenable and SAC
     for the preimage `H_E` of every finite `E <= A`. Every finite-index subgroup
     of `SL_3(Z)` has property (T), so `A` is finite. Then `E = A` gives
     `H_E = G`, and the hypothesis contains the conclusion.
   - **Euler characteristic.** Theorem 4.1 needs the kernel `H` to have a finite
     classifying space and `chi(H) = +-1`. By property (T), `H` has finite index,
     and a finite classifying space makes it torsion-free. Such `H` have
     `chi(H) = [SL_3(Z):H] chi(SL_3(Z)) = 0`, by Harder's formula with
     `zeta(-2) = 0`.
   - **Cohomological completeness.** Theorems 1.7 and 4.60 need `H` to be
     cohomologically complete (Definition 4.3): `H^*(Hhat^p, Z/p) -> H^*(H, Z/p)`
     is an isomorphism for every prime `p`. This fails for every torsion-free
     finite-index `H`, where `cd H = 3`.
     - If every `Hhat^p` is trivial, then `H` is `Z/p`-acyclic, so `chi(H) = 1`,
       not 0.
     - Otherwise some `Hhat^p` is nontrivial. By the congruence subgroup
       property it is finite, or `p`-adic analytic of dimension 8. So its mod-`p`
       cohomological dimension is infinite or 8, while the isomorphism forces
       it to be at most 3.
5. **Farkas--Linnell with torsion** (arXiv:math/0511747). Theorems 1.1--1.3 and
   6.1 assume a torsion-free group, and they cannot be extended.
   - An element `g` of order `n > 1` gives `(1 - g)(1 + g + ... + g^(n-1)) = 0`,
     so no division ring contains `C[G]`. The proof of Theorem 6.1 uses the
     finite cohomological dimension of a torsion-free pro-`p` group.
   - So the method sees only torsion-free open subgroups, which attempt 2 caps
     at 48. Jaikin-Zapirain's base change from `Qbar` to `C` does not change the
     denominator.
   - Allowing torsion does not help at odd primes.
     `sl3-zp-open-subgroup-lcm-index-bounds-for-strong-atiyah` shows
     `v_2(lcm W) + v_2([SL_3(Z_p):W]) >= 4` for every open `W` and odd `p`.
   - A `p`-adic input reaching 24 must be SAC with denominator 8 for a 2-adic
     open subgroup with torsion. The pro-2 Iwahori `I` (lcm 8, index 21) would
     suffice. Neither source gives that. Farkas--Linnell needs torsion-free
     groups. Linnell--Schick's criteria need a finite classifying space, or
     reduce to the same question as in attempt 4.
6. **Where the factor 2 is lost.** Restricting to torsion-free subgroups gives
   denominator 16 over `K_I` and over `K''`, and so 48 over `SL_3(Z)`. Here `K''`
   has index 351 and is the preimage of a Sylow 2-subgroup of `SL_3(F_3)`. The
   target for a new idea is `8 rk_{K_I}(B) in Z` for every matrix `B` over
   `C[K_I]`.
   - **Crossed-product form.** `Gamma(4) <= K_I` has index `2^11` and integer
     ranks. So by Linnell--Schick Lemma 2.3 and Proposition 2.2, `D(K_I)` is
     semisimple Artinian, and the target says `8 tr(e) in Z` for every
     projection `e` in `D(K_I)`. What is known is `16 tr(e) in Z`.
   - **A sufficient condition.** SAC for the pro-2 Iwahori `I`, as a discrete
     group, implies the target by induction from `K_I` to `I`.
