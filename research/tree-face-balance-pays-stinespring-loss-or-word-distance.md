---
rg: 2
id: tree-face-balance-pays-stinespring-loss-or-word-distance
kind: claim
title: Every triangular ucp balance pays Stinespring leakage or leaves every group-word lift on one tree face
distinct_from:
  tree-face-balance-pays-word-or-multiplicative-defect: that uses an abstract multiplication defect; this replaces it by the intrinsic Kadison--Schwarz slack, equivalently the norm of the Stinespring off-corner on a face unitary.
  kernel-relator-forces-two-edge-ucp-section-gap: that measures displacement from canonical closing-face letters; this measures failure of the two tree faces to enter the multiplicative domain, unless one stays far from every group-word lift.
  property-t-alone-cannot-correct-tracial-choi-lifts: that is a general no-go for manufacturing coordinatewise ucp lifts from property T; this is a concrete operator-norm alternative obeyed by every already-ucp balance at the explicit triangle.
---

**ESTABLISHED (intrinsic Stinespring form).**  At the explicit `(3,3,4)`
triangle, use `Phi`, `gamma_V`, and the fixed nontrivial closing-face
kernel-relator length `L` from
`tree-face-balance-pays-word-or-multiplicative-defect`.  For
`V in {P_12,P_23}` define the Kadison--Schwarz slack

```text
sigma_V=max_(g in V) ||1-Phi(u_g)^*Phi(u_g)||,
delta_L=min{sqrt(2),6/L^2}.                                (SMD1)
```

Then

```text
max_V (sqrt(sigma_V)+3 gamma_V) >= delta_L.                (SMD2)
```

Consequently one of the two tree faces satisfies

```text
sigma_V >= delta_L^2/4       or       gamma_V >= delta_L/6. (SMD3)
```

In a Stinespring realization `Phi(x)=W^* pi(x)W`, `P=WW^*`, the first
quantity is exactly

```text
sigma_V=max_(g in V) ||(1-P)pi(u_g)W||^2.                 (SMD4)
```

Thus the surviving nonmultiplicative branch is not merely failure of a
chosen product identity.  Unless a face stays macroscopically far from every
group-unitary lift, one canonical finite-face unitary sends the Stinespring
corner a fixed distance outside itself.  Equivalently, that unitary has a
fixed failure of the multiplicative-domain identity for `Phi`.

Proof: `tree-face-stinespring-loss-dichotomy-proof`.

**Exact scope.**  This is a no-go, not a construction and not a contradiction
to local ucp splitting.  A finite relator reservoir may support the required
off-corner.  The result says any successful reservoir must do so at a fixed
scale; a Newton scheme whose iterates converge into the multiplicative domain
of word-valued tree faces cannot close the triangle.

DERIVATION
tree-face-stinespring-loss-dichotomy-proof
