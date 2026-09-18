---
rg: 2
id: deligne-lattice-non-mf-forces-finite-parameter-group
kind: claim
title: Deligne's universal-cover lattice is MF on the full parameter circle, and on a finite parameter group its MF radical is trivial or exactly the period power of the center
distinct_from:
  deligne-sep7-all-cover-mf-radical-classification: that computes the MF radicals of the finite covers E_q and explicitly makes no claim about E_infinity, whose central unitary need not have finite spectrum; this treats E_infinity itself, proves one direction outright, the radical dichotomy {1, <z^m>}, the arc-spectrum constraint, and reduces the other direction to one instance of commutant-projection-extraction.
  deligne-sep7-norm-parameter-closed-subgroup: that proves P_op is a closed subgroup containing 1/2; this converts the full-circle alternative into an injective corona model of the Deligne lattice and the finite alternative into a spectral constraint on every corona model of it.
  dogon-sp2g-weak-ucp-nonhyperlinear: that makes the same lattice non-hyperlinear under weak ucp-stability of the base; this is about operator-norm MF of the lattice and ties it to the Maslov norm-parameter group, with no stability hypothesis.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records property (T) and the failure of residual finiteness; this is about the operator-norm corona radical of the same group.
  commutant-projection-extraction: that is the general open corner question for central unitaries in a matrix corona; this names the single instance (Gamma~, z^m) that would upgrade the one-way implication here to an equivalence.
---

**ESTABLISHED** (route `deligne-lattice-non-mf-forces-finite-parameter-group-proof`).

**Setting.** `Gamma = Sp_4(Z)`, `E_infinity = Gamma~` is the preimage of `Gamma` in the universal cover of
`Sp_4(R)`, `z` is the central generator of the covering kernel, and `b`, `c_theta`, `P_op`, `f_W`, `B_W = max_W |b|`
are as in `deligne-sep7-norm-parameter-closed-subgroup` and `deligne-sep7-all-cover-mf-radical-classification`.
MF means an injective homomorphism into the unitary group of a norm matrix corona `Q`. `Rad_MF` is the intersection of
the kernels of all such homomorphisms. `mu_m` is the group of `m`-th roots of unity.

**Theorem.**
1. **Full circle gives MF.** If `P_op = R/Z`, then `Gamma~` is MF. Equivalently: if `Gamma~` is not MF, then
   `P_op = (1/m)Z/Z` for one even `m`. One irrational parameter in `P_op` already suffices.
2. **Corner lemma.** Let `Theta : Gamma~ -> U(Q)` be a homomorphism, `q` a nonzero projection in the relative
   commutant `Theta(Gamma~)' cap Q`, and `lambda = exp(2 pi i psi)` with `||(Theta(z) - lambda) q|| <= eta`.
   Then `f_W(psi) <= B_W eta` for every finite window `W`.
3. **Radical dichotomy.** Suppose `P_op = (1/m)Z/Z`. Then `Rad_MF(Gamma~)` is either trivial or exactly `<z^m>`.
   Also `Gamma~/<z^m> = E_m` is MF.
4. **Arc constraint.** Suppose `P_op = (1/m)Z/Z`, and let `Theta` be any corona homomorphism of `Gamma~`. Then every
   point `lambda` of `sp(Theta(z))` with `lambda^m != 1` lies in a nondegenerate connected component of
   `sp(Theta(z))`, that is, an arc or the whole circle. So if `Theta(z)^m != 1`, then `Theta(z)` has infinite order
   and its spectrum contains a nondegenerate arc on which no commutant corner localizes `Theta(z)` near a scalar.
5. **Conditional converse.** Let `(CPE*)` be the contrapositive form of `commutant-projection-extraction` for
   `H = Gamma~`, `eps = z^m`:
   if `||Theta(z^m) - 1|| >= delta > 0`, then for every `eta > 0` there are a nonzero projection
   `q in Theta(Gamma~)' cap Q` and `mu in sp(Theta(z^m))` with `|mu - 1| >= delta` and
   `||(Theta(z^m) - mu) q|| <= eta`.
   If `P_op = (1/m)Z/Z` and `(CPE*)` holds, then `Rad_MF(Gamma~) = <z^m>`. So, granting `(CPE*)`,
   `Gamma~` is MF iff `P_op = R/Z` iff every finite cover `E_q` is MF.
6. **Flagship decomposition.** `deligne-triple-cover-exact-mf-radical` follows from two prerequisites, each of which
   can fail on its own (route `deligne-triple-cover-via-deligne-lattice-non-mf`):
   - (i) `deligne-universal-cover-lattice-is-not-mf`: a parameter-free statement about one named Kazhdan lattice;
   - (ii) `deligne-finite-parameter-group-has-period-prime-to-three`.
   Granting `(CPE*)`, the flagship also implies (i). So (i) is then exactly the finite-parameter half.

**What this changes.**
- The finite-parameter half of the flagship can be attacked as "Deligne's non-residually-finite lattice is not MF",
  with no cover, no parameter and no cocycle. This is the operator-norm analogue of the question Dogon attacks in the
  tracial setting (`dogon-sp2g-weak-ucp-nonhyperlinear`).
- Item 4 says what a refutation of (i) must look like when `P_op` is finite: a corona model in which the central
  unitary has an arc of spectrum away from `mu_m`, with no commutant corner cutting that arc. That is exactly the
  residual configuration of `commutant-projection-extraction`. Models built from exact or finite-order central data
  (direct sums of sector models, finite quotients, rounded spectra) can never separate `z^m`.
- Item 3 rules out intermediate radicals `<z^(km)>`, `k >= 2`: a corona model that kills any power of `z` kills `z^m`.
