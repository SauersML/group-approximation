---
rg: 2
id: promislow-fp-has-nontrivial-shadow-monomial-units
kind: claim
title: For p = 2, 3, 5, 7 the group ring F_p[P] has nontrivial units whose three definite shadows are all signed monomials
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that proves integral units have monomial definite shadows; this shows nontrivial units of F_p[P] can have the same property, so in characteristic p it does not single out trivial units.
  promislow-classical-nontrivial-units-have-no-integral-lifts: that shows the known nontrivial units have non-monomial shadows; this builds nontrivial units from them whose shadows are all monomials.
  promislow-unit-conjecture-from-shadow-monomial-fp-units: that derives Higman's conjecture for P from triviality of shadow-monomial units for infinitely many primes; this shows that hypothesis fails at p = 2, 3, 5, 7.
---

**ESTABLISHED** (hand argument plus exact computation). Let `P` be the Promislow
group, with definite shadows `C, A, B` as in
`promislow-integral-units-have-monomial-definite-line-shadows`.

1. **`p = 2`.** For `h = diag(e_1, e_2, e_3)` with signs `e_i`, conjugation by `h`
   in Gardam's affine model is an automorphism `sigma_h` of `P`. Let `u` be
   Gardam's unit of `F_2[P]`. Then `v_h = u sigma_h(u)^-1` is a nontrivial unit of
   `F_2[P]` with all three shadows signed monomials, for `h = diag(1,1,-1)`,
   `diag(-1,1,1)` and `diag(-1,1,-1)`. The supports have sizes `109`, `61` and
   `73`.
2. **`p = 3, 5, 7`.** Let `u` be any of Murray's Theorem 3 units of `F_p[P]`
   (`murray-z-only-ansatz-has-no-char0-units`, eight parameter pairs), and
   `z = (ab)^2`. The commutator `[u, z] = u z u^-1 z^-1` is a nontrivial unit of
   `F_p[P]` whose three shadows are signed monomials. Among the 64 elements
   `sigma_h(u)`, 384 of the 4032 ordered quotients `w_1 w_2^-1` for each `p` are
   also nontrivial units with monomial shadows.

**Mechanism in item 2.**
- Every Murray unit has a monomial shadow on line `C` (computed in
  `promislow-classical-residues-shadow-computation`).
- `z` maps to `t^2` on `C` and to the central element `-1` on `A` and `B`.
- So the shadows of `[u, z]` are `1` on `A` and `B`, and the monomial `m t^2 m^-1 t^-2`
  on `C`.
- Only nontriviality needs computation.

**Consequence.** Monomial definite shadows do not force a unit of `F_p[P]` to be
trivial for any of `p = 2, 3, 5, 7`. So the hypothesis of item 1 of
`promislow-unit-conjecture-from-shadow-monomial-fp-units` fails at all four
primes. Shadow information in characteristic `p` cannot close Case A of Higman's
conjecture for `P`; a proof has to use characteristic-zero structure beyond the
three shadows.

**Scope.** Primes `p > 7` were not computed. Item 2 extends to every odd `p` for
which Murray's unit has a monomial `C` shadow and does not commute with `z` up to
a trivial unit. That was checked only for `p <= 7`. No novelty is claimed.

DERIVATION
[[promislow-fp-shadow-monomial-units-computation]]
