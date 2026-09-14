---
rg: 2
id: promislow-nonzero-twisted-classes-have-no-definite-shadows
kind: claim
title: The definite dihedral shadows exist only at the zero class, because the relator signs of a nonzero twisted Promislow ring force an eighth root of unity
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that constructs the three definite shadows of Z[P] and proves units are monomial in them; this shows the twisted rings of the three nonzero classes admit no homomorphism into D(Z), or into any degree-2 algebra over a formally real field without sqrt(2), and locates the class in Step 1 of that proof.
  promislow-twisted-integral-rings-carry-gardam-units: that classifies the four twisting classes and shows the nonzero ones carry nontrivial units; this gives a gauge-invariant sign invariant of the class and proves why those units escape the shadow argument.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture; this proves no triviality and only isolates which input sees the zero class.
artifacts:
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14.md
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14/class_shadow_check.py
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14/class_shadow_check-run.log
---

**ESTABLISHED** by `promislow-twisted-class-definite-shadow-obstruction-proof`.
Unreviewed. No novelty is claimed; the arguments are elementary.

**Setting.** `P = <a, b | b^-1 a^2 b a^2 = 1, a^-1 b^2 a b^2 = 1>` is the
Promislow group. For a normalized 2-cocycle `c: P x P -> {+-1}`, `Z^c[P]` is the
twisted integral group ring with basis `gbar` and `gbar hbar = c(g,h) (gh)bar`.
`D(R) = R[t^(+-1)]<u | u^2 = -1, u f(t) = f(t^-1) u>` as in
`promislow-integral-units-have-monomial-definite-line-shadows`.

1. **Relator signs.** In `Z^c[P]` define `kappa_1(c), kappa_2(c) in {+-1}` by

       bbar^-1 abar^2 bbar abar^2 = kappa_1 * 1bar,     abar^-1 bbar^2 abar bbar^2 = kappa_2 * 1bar.

   They depend only on `[c]`. The map `kappa = (kappa_1, kappa_2)` is a group
   isomorphism `H^2(P; Z/2) -> {+-1}^2`. In the notation of
   `promislow-twisted-integral-rings-carry-gardam-units`,
   `kappa(e_1 beta(rho_1) + e_2 beta(rho_2)) = ((-1)^e_1, (-1)^e_2)`. Gardam's
   class `beta(rho_1 + rho_2)` has `kappa = (-1, -1)`.
2. **The obstruction.** If `kappa_1(c) = -1` and `phi: Z^c[P] -> A` is a unital
   ring homomorphism, then `h = phi(abar)` and `k = phi(bbar)^-1` satisfy
   `k h^2 k^-1 = -h^-2` in `A^x`. If `kappa_2(c) = -1`, the same holds with
   `h = phi(bbar)` and `k = phi(abar)^-1`.
3. **Degree-2 targets.** Let `A` be a central simple algebra of degree 1 or 2
   over a field `F` of characteristic not 2. If `h, k in A^x` satisfy
   `k h^2 k^-1 = -h^-2`, then `-1` is a square in `F` or `h^4 = -1`. In the
   second case `X^4 + 1` has a factor of degree at most 2 over `F`, so one of
   `-1, 2, -2` is a square in `F`. Hence, **for `[c] != 0` there is no unital ring
   homomorphism from `Z^c[P]` to a central simple algebra of degree at most 2
   over a formally real field that does not contain `sqrt(2)`.**
4. **Only the zero class has definite shadows.** `D(Z)` lies in the cyclic
   algebra `D(Q(t))`, of degree 2 over the formally real field `Q(t + t^-1)`,
   which does not contain `sqrt(2)`. So for `[c] != 0` there is no unital ring
   homomorphism `Z^c[P] -> D(Z)`. For `[c] = 0` the shadows `A`, `B`, `C` are
   such homomorphisms. In the route `promislow-definite-line-shadow-parseval-proof`,
   the class therefore enters only at Step 1 (both relators map to `+1` with no
   sign). Steps 2–4 (kernel count, multiplicative norm, sum of squares) apply to
   any ring homomorphism into `D(Z)` and are class-blind.
5. **Where `zeta_8` enters.** For the class with `kappa = ((-1)^e_1, (-1)^e_2)`,
   `abar -> zeta_8^e_1 u` and `bbar -> -zeta_8^e_2 t^-1 u` define a unital ring
   homomorphism `Z^c[P] -> D(Z[zeta_8])`. It is the gauge map of item 5 of
   `promislow-twisted-integral-rings-carry-gardam-units` followed by shadow `C`.
   There `h = zeta_8 u` satisfies `h^2 = -h^-2`, as item 3 requires.

**Consequence for the integral problem on `P`.** Any proof that every unit of
`Z[P]` is trivial must use an input that fails for the nonzero classes.
Homomorphisms into degree-2 algebras over formally real fields without
`sqrt(2)` are exactly such inputs, and `D(Z)` is one of them. On the lines of
`K4`-fixed characters other than the three definite ones the quotient algebras
are of this kind too, but their unit groups are infinite (e.g. `1 + (1-a)b(1+a)`
in `Z[P/<x,y>] = Z[D_inf]`, checked in the artifact), so class-sensitivity alone
gives no rigidity there. What remains is recorded in
`promislow-dihedral-ring-homomorphisms-are-the-three-shadows`.

**Checks.** `class_shadow_check.py` runs in exact integer arithmetic on MSI:
- the relator signs of the four twisted models (item 1);
- no solution of `k h^2 k^-1 = -h^-2` in `D(Z)^x` on a box of 36 monomials (item 4);
- the homomorphisms `Z^c[P] -> D(Z[zeta_8])` and the witness `h = zeta_8 u` (item 5).

DERIVATION
[[promislow-twisted-class-definite-shadow-obstruction-proof]]
