---
rg: 2
id: symmetrize-separator-and-test-liftable-face-expectations
kind: route
title: Average only compatible automorphisms and rule out one-face-local separators
target: three-face-quotient-separators-are-not-one-face-local
requires:
  - explicit-finite-face-ucp-section-is-edge-equivariant
  - group-word-tree-face-balancing-collapses
---

## 1. Compatible symmetry averaging preserves the gap

For a self-adjoint map `psi:S_Delta->Q`, define

```text
(omega psi)=beta_omega^(-1) o psi o beta_omega|_(S_Delta).
```

Put

```text
ell_Omega(psi)=|Omega|^(-1) sum_(omega in Omega)ell(omega psi). (1)
```

This functional is `Omega`-invariant.  If `phi:S_Delta->A` is ucp, then

```text
phi_omega=alpha_omega^(-1) o phi o beta_omega|_(S_Delta)
```

is ucp and compatibility `(SQS3)` gives

```text
q phi_omega=beta_omega^(-1) o(q phi)o beta_omega.
```

The identity map is fixed by this action.  Therefore

```text
ell_Omega(id-q phi)
 =|Omega|^(-1) sum_omega ell(id-q phi_omega)>=delta,       (2)
```

proving the first assertion without changing the separation constant.

## 2. Every face expectation is liftable

For a subgroup `H<=Lambda`, its characteristic function `1_H` is positive
definite: it is the coefficient of the quasi-regular representation on
`ell^2(Lambda/H)` at the coset `H`.  Hence the Fourier multiplier `(SQS4)` is
ucp on the full group C-star algebra.  Its range is `C^*(H)` and it is the
identity there.

For `H=P_12` or `P_23`, let `j_H:C^*(H)->A` be the canonical star
homomorphism.  Then

```text
Phi_H=j_H o M_H|_(S_Delta)
```

is ucp and `q Phi_H=M_H`.  For `H=P_13`, let
`Theta_13:C^*(P_13)->C^*(P_1*_(P_0)P_3) subset A` be the ucp section from
`explicit-finite-face-ucp-section-is-edge-equivariant`, and put

```text
Phi_13=Theta_13 o M_(P_13)|_(S_Delta).
```

Again `Phi_13` is ucp and `q Phi_13=M_(P_13)`.  Substitution in `(SQS2)` gives
`(SQS5)`.

If `ell` factors through restriction to `C^*(H)`, then it vanishes on every
map whose restriction to `C^*(H)` is zero.  But `id-M_H` has exactly that
property, contradicting `(SQS5)`.  This proves `(SQS6)`.  Since every entry
of the kernel prefix Gram matrix belongs to `C^*(P_13)`, every scalar linear
functional obtained by pairing that matrix with a matrix functional factors
through the `P_13` restriction and is excluded.

## 3. Scope of the conclusion and the actual symmetry group

No face-component decomposition is used here.  In particular, although
`S_Delta` is the algebraic vector-space sum of the three face algebras, it is
infinite-dimensional.  Assigning a Hamel basis vector to one face does not
produce a bounded splitting of the restriction map, so it does not decompose
a bounded functional on `L_sa(S_Delta,Q)` into bounded face functionals.
The valid conclusion is exactly `(SQS6)`: `ell` cannot factor boundedly
through any single face restriction.

The unique Coxeter label `4` in the `(3,3,4)` diagram forces every actual
diagram automorphism to fix the `13` face and permits at most the swap of the
two type-`3` faces.  This constrains the averaging group but, without a
separate bounded-splitting theorem, does not yield a closing-plus-tree normal
form for the averaged functional.

For completeness, consider inner symmetries of the marked triangle.  The
maximal spherical rank-two parabolics are self-normalizing in the explicit
candidate, as verified in `group-word-tree-face-balancing-collapses`.  An
element of `Lambda` normalizing `P_12`, `P_23`, and `P_13` therefore belongs
to

```text
P_12 intersect P_23 intersect P_13=P_0.                  (3)
```

If an inner symmetry permutes faces, compose it with the corresponding actual
diagram automorphism first and apply `(3)`.  Thus the finite standard inner
action available for `(1)` is the common `P_0` conjugation action (possibly
extended by diagram automorphisms).  An independent conjugation by a whole
face group preserves that face but not the other two summands of `S_Delta`,
so it is not an action on the map space in `(SQS2)`.  This proves the final
scope statement.
