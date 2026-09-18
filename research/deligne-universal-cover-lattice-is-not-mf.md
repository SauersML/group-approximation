---
rg: 2
id: deligne-universal-cover-lattice-is-not-mf
kind: claim
title: Deligne's non-residually-finite Kazhdan lattice in the universal cover of Sp4(R) is not MF
distinct_from:
  dogon-sp2g-weak-ucp-nonhyperlinear: that makes the same lattice non-hyperlinear (a tracial statement) under weak ucp-stability of the base; this asks for operator-norm non-MF with no hypothesis. Non-hyperlinear does not formally give non-MF in the weak corona convention, nor conversely.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records property (T) and failure of residual finiteness; this asks for the strictly stronger failure of norm-corona approximation.
  sp4-quasirep-windings-are-sublinear: that is a statement about plain quasi-representations of Sp_4(Z) excluding the full parameter circle; this is a statement about the lattice itself, and by deligne-lattice-non-mf-forces-finite-parameter-group it implies finiteness of P_op but is not known to be implied by it without commutant-projection-extraction.
  deligne-lattice-non-mf-forces-finite-parameter-group: that is the established theorem relating this claim to P_op; this is the open statement itself.
  commutant-projection-extraction: that is a general corner question for central unitaries; this is a single group-theoretic statement to which it would reduce the finite-parameter branch.
---

**OPEN.** Let `Gamma~ = E_infinity` be the preimage of `Sp_4(Z)` in the universal cover of `Sp_4(R)`. The claim is
that `Gamma~` is not MF: every homomorphism from `Gamma~` into the unitary group of a norm matrix corona has nontrivial
kernel. Equivalently, `Rad_MF(Gamma~) != {1}`.

Equivalent forms, by `deligne-lattice-non-mf-forces-finite-parameter-group`:
- `Rad_MF(Gamma~) = <z^m>`, where `P_op = (1/m)Z/Z`. There is no intermediate radical, and `m` is then forced to be
  finite.
- The same statement for the torsion-free, finitely presented, Kazhdan finite-index subgroup `Gamma~(3)` (remark in the
  proof route).

**Why it matters.**
- It implies `P_op = (1/m)Z/Z` with `m` even (item 1 of the theorem). With
  `deligne-finite-parameter-group-has-period-prime-to-three`, it gives the flagship
  `deligne-triple-cover-exact-mf-radical`, via route `deligne-triple-cover-via-deligne-lattice-non-mf`.
- Granting the single instance `(CPE*)` of `commutant-projection-extraction`, it is equivalent to `P_op` being finite.
  So it is then equivalent to the finite-parameter half of every existing route. That includes
  `sp4-quasirep-winding-ratio-has-a-deficit`, which implies it under `(CPE*)`.
- It is the operator-norm analogue of the tracial question on the same lattice studied through
  `dogon-sp2g-weak-ucp-nonhyperlinear`. It concerns one named group, with no cover, parameter or cocycle in the
  statement.

**How it can fail.**
- `P_op = R/Z` refutes it (item 1 of the theorem). One irrational norm-parameter suffices.
- If `P_op` is finite, a refutation must be a corona model `Theta` with `Theta(z)^m != 1`. By item 4 of the theorem,
  `sp(Theta(z))` then contains a nondegenerate arc through a point `lambda` with `lambda^m != 1`, and no commutant
  corner localizes `Theta(z)` near a scalar off `mu_m`. That is the residual arc configuration of
  `corona-corner-detection-criterion`.
- None of the following can refute it: direct sums of sector models, finite quotients, and models whose central unitary
  has finite or totally disconnected spectrum.

## Attempts
- **2026-09-18, swarm-0917-w8-w8-deligne-break (operator-algebras): posed.** It is reduced to and from `P_op` by
  `deligne-lattice-non-mf-forces-finite-parameter-group`. No direct attack has been made. The dimension-growth and
  Kazhdan-rigidity inputs from `normal-kazhdan-defect-non-mf` do not apply as stated: `z` is central of infinite
  order, and `Gamma~` is not residually finite, so no finite quotient sees `z`.
