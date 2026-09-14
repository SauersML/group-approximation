---
rg: 2
id: promislow-twisted-integral-rings-carry-gardam-units
kind: claim
title: Gardam's complex unit is a unit of the twisted integral group ring of a nonzero class in H^2(P;Z/2), and Higman's conjecture on P is the zero class
distinct_from:
  unit-conjecture-fails-over-complex-numbers: that imports nontrivial units of C[P] with coefficients in Z[zeta_8]; this shows those units are units of twisted group rings over Z itself, and classifies the four twisting classes.
  integral-unit-conjecture-torsion-free: that is Higman's open conjecture for every torsion-free group; this identifies its instance on P with the zero class and proves that the three other classes fail.
  promislow-radius4-support-pairs-need-zeta8: that computes which characteristic-zero fields carry units on 52 fixed support pairs; this is a cohomological explanation of where zeta_8 enters, valid at every support.
  integral-group-ring-units-have-arithmetically-large-spectra: that is a necessary spectral condition on nontrivial units of Z[G]; this exhibits integral twisted rings of P, with the same integrality and trace structure, that do carry nontrivial units.
artifacts:
  - research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14.md
  - research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14/twisted_integral_unit_check.py
  - research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14/twisted_integral_unit_check-run.log
---

**ESTABLISHED** by `promislow-twisted-integral-rings-gardam-units-proof`.
Unreviewed. It repackages the monomial grading of Gardam's unit (Gardam,
arXiv:2312.05240, Remark 2, as recorded in the attempt "Untwisting Gardam's
unit" of `integral-unit-conjecture-torsion-free`). The classification of the
twisting classes is new here as far as main records.

**Setting.** `P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>` is the
Promislow group. For a 2-cocycle `c: P x P -> {+-1}`, the twisted integral
group ring `Z^c[P]` is the free abelian group on symbols `gbar` (`g in P`) with
`gbar hbar = c(g,h) (gh)bar`. Its *trivial units* are `+-gbar`. Identify
`{+-1}` with `Z/2`, and let `beta: H^1(P; Z/4) -> H^2(P; Z/2)` be the Bockstein
of `0 -> Z/2 -> Z/8 -> Z/4 -> 0`.

1. **The classes.** `P^ab = Z/4 + Z/4`, and `beta` induces an isomorphism
   `H^1(P; Z/2) -> H^2(P; Z/2) = (Z/2)^2`. Up to isomorphism `Z^c[P]` depends
   only on `[c]`, through a support-preserving isomorphism that sends trivial
   units to trivial units.
2. **Zero class.** If `[c] = 0` then `Z^c[P] = Z[P]` by `gbar -> h(g) g` for some
   `h: P -> {+-1}`. So "every unit of `Z^c[P]` is trivial" for the zero class is
   exactly Higman's conjecture on `P` (open;
   `integral-unit-conjecture-torsion-free`).
3. **Gardam's unit is twisted integral.** Let `rho: P -> (Z/4)^2` be the
   homomorphism with `rho(a) = (1,0)` and `rho(b) = (0,1)`. Write `it(g)`,
   `jt(g)` in `{0,1,2,3}` for the entries of `rho(g)`, and put

       c(g,h) = (-1)^([it(g)+it(h) >= 4] + [jt(g)+jt(h) >= 4]).

   Then `c` is a cocycle with `[c] = beta(rho_1 + rho_2) != 0`. Write Gardam's
   unit and its inverse in `R[P]`, `R = Z[s,t]/(s^4+1, t^4+1)`, with
   coefficients `eps_g s^it(g) t^jt(g)` and `eps_g in {+-1}`. Then
   `abar = sum eps_g gbar` is a unit of `Z^c[P]` with 21 coefficients `+-1`.
   Its inverse is built the same way from Gardam's inverse.
4. **All nonzero classes fail.** For each of the three nonzero classes `[c]`,
   `Z^c[P]` has a nontrivial unit with coefficients `+-1` and support of size
   21. The automorphism `a -> b, b -> ab` of `P` permutes the three classes
   cyclically.
5. **Back to Z[zeta_8].** For any homomorphism `rho: P -> (Z/4)^2` with
   cocycle `c` as in item 3, `ubar -> sum u_g zeta_8^(it(g)+jt(g)) g` sends
   units of `Z^c[P]` to units of `Z[zeta_8][P]`, preserving supports. So a
   nontrivial unit of a twisted ring of a nonzero class is the same thing as
   a nontrivial unit of `Z[zeta_8][P]` whose coefficients are signed eighth
   roots of unity arranged along a homomorphism.

**Consequences.**
- On `P`, Higman's conjecture fails for three of the four twisted integral
  group rings and is open for the fourth. A proof has to distinguish the zero
  class. Two inputs apply verbatim to every `Z^c[P]` and so cannot do that
  alone:
  - reduction modulo primes, to `F_p^c[P]`;
  - the trace identity `tau(ubar ubar*) = sum u_g^2` for the involution
    `gbar* = gbar^-1`.
- Over a field `K` containing `zeta_8`, every class becomes a coboundary
  (`f(g) = zeta_8^(it(g)+jt(g))`), so `K^c[P] = K[P]`. This is where `zeta_8`
  enters in `unit-conjecture-fails-over-complex-numbers`. The support-by-support
  statements of `promislow-radius4-support-pairs-need-zeta8` are not implied.

DERIVATION
[[promislow-twisted-integral-rings-gardam-units-proof]]
