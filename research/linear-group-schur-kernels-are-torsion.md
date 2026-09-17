---
rg: 2
id: linear-group-schur-kernels-are-torsion
kind: claim
title: Over a finitely generated linear group, every nonsingular one-variable adjunction kills only torsion in second homology
distinct_from:
  aspherical-adjunction-has-zero-schur-kernel: that kills the whole Schur kernel for aspherical relative presentations over any group; this allows every equation shape and kills the rational Schur kernel over linear coefficient groups.
  amenable-coefficients-have-zero-schur-kernel: that localizes to amenable coefficient packets; this uses the coefficient group itself, which is linear and may be non-amenable.
  projective-unitary-classes-vanish-on-schur-kernel: that pairs exact projective homomorphisms with the kernel; this pairs asymptotic homomorphisms, which detect every non-torsion class of a linear group.
  schur-kernels-are-invisible-to-matricial-windings: that is the vanishing theorem for any group; this combines it with Dadarlat's detection theorem for linear groups.
---

**Theorem.** Let `Gamma` be a finitely generated linear group, and let
`w in Gamma * <t>` have `deg_t(w) != 0`. Then

    K_2(Gamma, w) = ker( H_2(Gamma; Z) -> H_2((Gamma * <t>)/<<w>>; Z) )  <=  Tors H_2(Gamma; Z).

Equivalently, `H_2(Gamma; Q) -> H_2((Gamma * <t>)/<<w>>; Q)` is injective.
Also, in the notation of `schur-kernels-are-invisible-to-matricial-windings`,
`Rig(Gamma) = Tors H_2(Gamma; Z)`.

**Corollary (multipliers with torsion-free coefficients).** Let `A` be an
abelian group, `alpha in H^2(Gamma; A)`, and
`alpha_H : H_2(Gamma; Z) -> A` its evaluation. Suppose that `A` is
torsion-free, or that `alpha` is the image of a class
`beta in H^2(Gamma; B)` under a coefficient map `B -> A` with `B`
torsion-free. Then `alpha_H(K_2(Gamma, w)) = 0` for every nonsingular `w`.
In particular this holds for every reduction `e mod n` of an integral class
`e in H^2(Gamma; Z)`.

*Proof of the corollary.* Evaluation is natural in the coefficients:
`alpha_H = (B -> A) o beta_H`. A homomorphism from a torsion group into a
torsion-free group is zero, so `beta_H` vanishes on `K_2`. ∎

**Scope.** The proof uses only the conclusion of Dadarlat's Theorem 3.2
(quoted verbatim in `dadarlat-linear-groups-have-nonzero-h2-windings`).
So the Theorem and Corollary hold word for word for every countable
quasidiagonal group that admits a gamma-element. The group `Gamma` need not
be finitely presented, and `w` is
arbitrary with nonzero exponent sum. The torsion part of `K_2` is not
constrained. For a multiplier with torsion coefficients that does not lift to
torsion-free coefficients, it can still be seen by `alpha_H`.

DERIVATION
linear-group-schur-kernels-are-torsion-proof
