---
rg: 2
id: schur-kernels-are-invisible-to-matricial-windings
kind: claim
title: Matricial Exel--Loring windings vanish on the Schur kernel of every nonsingular adjunction
distinct_from:
  projective-unitary-classes-vanish-on-schur-kernel: that kills the multiplier of an exact projective homomorphism into a corona unitary group, a Z/n- or circle-valued primary class; this kills the integer-valued secondary winding of asymptotic homomorphisms into matrices, which is invisible to every exact homomorphism.
  exel-loring-relative-quasirep-invariant: that imports Dadarlat's H_2 pairing of quasi-representations and its nontriviality theorem for quasidiagonal groups; this proves the pairing is identically zero, at small defect and in every dimension, on classes killed by a one-variable nonsingular equation.
  nonsingular-equations-preserve-matrix-certificates: that transports operator-norm relator inequalities across an adjunction; this transports an integer invariant and uses only the exact root in U(d) supplied there.
  exel-loring-mark-quantization: that deploys the winding against a central mark of a non-MF candidate and is blocked by multiplicativity; this uses honest asymptotic homomorphisms of the base group and no mark.
---

**Setting.** Let `Gamma = F/R` with `F = F(S)` and `R` the normal closure of
a set `R_0` of relators. A **Hopf word** is `h in R cap [F, F]`, with class
`[h] in H_2(Gamma; Z) = (R cap [F,F]) / [F, R]`. For `rho : S -> U(d)`,
extended to `F`, and a finite `P subset R_0`, put
`delta_P(rho) = max_{r in P} ||rho(r) - I||` (operator norm). When
`||rho(h) - I|| < 2`, set

    kappa(rho, h) = (1 / 2 pi i) Tr log rho(h)      (principal logarithm).

This is an integer, because `det rho(h) = 1` for `h in [F, F]`. For
`h = prod [a_i, b_i]` it is the right-hand side of Dadarlat's form of the
Exel--Loring formula (arXiv:2111.05755, Theorem 1.1, quoted in
`exel-loring-mark-quantization`). No part of that theorem is used here.

**Theorem.** Let `w in Gamma * <t>` have `deg_t(w) != 0`, let
`x in K_2(Gamma, w) = ker(H_2(Gamma) -> H_2((Gamma * <t>)/<<w>>))`, and let
`h` be any Hopf word for `x`. There are a finite `P subset R_0` and
`delta > 0`, depending only on `h` and a lift of `w`, such that

    kappa(rho, h) = 0   for every d and every rho : S -> U(d) with delta_P(rho) < delta.

**Class-level form.** Call `x in H_2(Gamma; Z)` **matricially winding-rigid**
if every asymptotic homomorphism `rho_n : S -> U(d_n)`, meaning
`delta_P(rho_n) -> 0` for each finite `P`, has `kappa(rho_n, h) = 0` for all
large `n`. This does not depend on the Hopf word. The rigid classes form a
subgroup `Rig(Gamma)` with three properties:

- `Rig(Gamma)` contains all torsion;
- if `m x in Rig(Gamma)` with `m != 0`, then `x in Rig(Gamma)`;
- `K_2(Gamma, w) <= Rig(Gamma)` for every nonsingular `w`.

It also equals `H_2(Gamma; Z)` whenever `Gamma` is matricially stable.

**Use.** A single asymptotic homomorphism into matrices with nonzero winding
on `x`, infinitely often, shows that no nonsingular one-variable equation
over `Gamma` kills any class in `x`'s rational line. That kills every
Schur-kernel certificate through that line.

DERIVATION
schur-kernel-winding-invisibility-proof
