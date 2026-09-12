---
rg: 2
id: iwahori-transfer-equals-matricial-commutant-codensity
kind: claim
title: Unitary Iwahori transfer is exactly relative-commutant co-density in matricial ultraproducts
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that proves commutant equality in every finite-dimensional exact representation of the amalgam; this characterizes the uniform strengthening over limits of almost-compatible finite vertex representations.
  iwahori-local-global-defect-question: that asks for metric repair of the two vertex representations; this asks only for equality of their relative commutants in the limiting matricial algebra.
  exact-first-hit-ladder-kills-regular-carrier: that rules out a trace-functorial positive-density ladder in the canonical group von Neumann algebra; this relative-commutant equality is allowed to hold in matricial ultraproduct representations without asserting any trace inequality in every finite von Neumann algebra.
---

Let `A=C_+*_(B_+=B_-)C_- = SL_2(Z[1/2])`.  The modulus in
`iwahori-unitary-commutant-transfer` exists if and only if the following
sequential relative-commutant statement holds.

For every sequence of dimensions `d_n`, exact representations
`pi_(n,+),pi_(n,-):C->U(d_n)` whose Iwahori edge defects tend to zero, every
free ultrafilter `omega`, and the induced homomorphism

```text
rho:A -> prod_omega (M_(d_n),tr_(d_n)),               (MRC1)
```

one has

```text
rho(C_+)' intersect M_omega
   =rho(A)' intersect M_omega.                        (MRC2)
```

Equivalently, a unitary in the matricial ultraproduct that commutes with the
first vertex also commutes with the second.

**Proof.**  If the modulus fails, choose a sequence with edge defect and
first-vertex commutators tending to zero but one second-vertex commutator
bounded below.  Its unitary ultraproduct gives an element of the left side of
`(MRC2)` outside the right side.  Conversely, a unitary violating `(MRC2)`
has representatives whose edge defects and first commutators tend to zero
while some second commutator does not, contradicting the modulus.  It is
enough to test unitaries because every von Neumann algebra is linearly
spanned by its unitaries; hence inclusion on unitary groups is inclusion of
the commutant algebras.  The reverse inclusion in `(MRC2)` is automatic.

Thus the new endpoint is not a hidden perturbation theorem.  It is a precise
matricial relative-commutant rigidity question for the Iwahori amalgam.
