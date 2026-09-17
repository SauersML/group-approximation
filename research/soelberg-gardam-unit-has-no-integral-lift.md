---
rg: 2
id: soelberg-gardam-unit-has-no-integral-lift
kind: claim
title: The Soelberg group has two definite dihedral shadows, and no unit of Z[S] reduces modulo 2 to Gardam's Soelberg unit
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that builds three definite shadows of the Promislow group P; this finds the definite shadows of the Soelberg group S, a different torsion-free group that is virtually Heisenberg and not virtually abelian, and shows there are exactly two of them up to automorphisms of D(Z).
  promislow-classical-nontrivial-units-have-no-integral-lifts: that excludes Gardam's unit of F_2[P] and other residues on P as reductions of integral units; this excludes Gardam's unit of F_2[S] (Theorem B of arXiv:2312.05240), the only other known nontrivial unit in characteristic 2 on a torsion-free group.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture for every torsion-free group; this removes only the lifts of one residue class, on the single group S.
  unit-conjecture-fails-over-complex-numbers: that is Gardam's complex unit on P; no characteristic-zero unit is known on S, and this rules out integral lifts of its F_2 unit.
artifacts:
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_engine.py
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_definite_shadows.py
  - experiments/soelberg-unit-lifting-2026-09-17/logs/soelberg_definite_shadows.log
---

**ESTABLISHED.** Let

    S = < x, y | (xy)^2 (xy^-1)^2 = 1,  (yx)^2 (yx^-1)^2 = 1 >

be the Soelberg group. It is torsion-free and virtually the integral Heisenberg
group (Gardam, arXiv:2312.05240v2, Section 4). Let `nu = sum(A) in F_2[S]` be
Gardam's unit of Theorem B. Here `A` is the list of 29 words in Gardam's
ancillary file, and `nu^-1 = sum(B)`. For a commutative ring `R`, let

    D(R) = R[t^(+-1)] < u | u^2 = -1, u f(t) = f(t^-1) u >,

with basis `t^m, t^m u`. This is the ring of
`promislow-integral-units-have-monomial-definite-line-shadows`.

1. **Shadows.** The assignments

       rho_1: x -> t, y -> u        rho_2: x -> u, y -> t

   extend to surjective ring homomorphisms `R[S] -> D(R)`. Take any group
   homomorphism from `S` to the signed monomials `{+-t^m, +-t^m u}` whose
   image spans `D(Z)`. It is `theta o rho_1` or `theta o rho_2` for an
   automorphism `theta` of `D(Z)` that permutes the signed monomials.
2. **Integral and rational units.** If `v` is a unit of `Z[S]`, then
   `rho_1(v)` and `rho_2(v)` are each of the form `+-t^m` or `+-t^m u`. If `v`
   is a unit of `Q[S]`, they are `lambda t^m` or `lambda t^m u` with
   `lambda in Q^x`.
3. **Lifting obstruction.** In `D(F_2)`,

       rho_1(nu) = rho_2(nu) = t^-2 + 1 + t^2 + (t^-2 + t^2) u,

   which is not a monomial. So no unit of `Z[S]`, and no unit of `Z_(2)[S]`,
   reduces modulo 2 to any of the following:
   - `nu`;
   - `g nu h` for `g, h in S`;
   - `alpha(nu)` for an automorphism `alpha` of `S`;
   - their inverses.

   Nothing is assumed about the support, the word radius or the coefficient
   height of the unit.

**Consequence for Higman's conjecture on S.** Write a unit of `Z[S]` with a
nontrivial residue modulo 2 as Case B. Gardam's unit, together with its
translates and automorphic images, is the only known nontrivial unit of
`F_2[S]`, and it is excluded as a Case B residue at every radius. Case A is
untouched: units congruent modulo 2 to a trivial unit. So is any other
nontrivial unit of `F_2[S]` whose two shadows are monomials.

**Contrast with P.** On `P` three shadows exist, and Gardam's complex unit
shows that positivity is essential there. On `S` the two shadows are
interchanged by Gardam's automorphism `phi: x -> y, y -> x^-1`, up to
`t -> t^-1`. No characteristic-zero unit of `S` is known.

**Credit.** The mechanism is the definite-shadow argument of
`promislow-integral-units-have-monomial-definite-line-shadows`, which is a
norm and a sum of squares. The new input is the pair of shadows of `S`, their
classification, and the exact images of Gardam's Soelberg unit. No novelty is
claimed for the method. Literature was not searched beyond Gardam
(arXiv:2312.05240v2) and the repo.

DERIVATION
[[soelberg-gardam-unit-has-no-integral-lift-proof]]
