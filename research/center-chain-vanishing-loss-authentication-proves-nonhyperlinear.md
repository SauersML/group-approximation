---
rg: 2
id: center-chain-vanishing-loss-authentication-proves-nonhyperlinear
kind: route
title: Turn vanishing-loss native authentication directly into the affine regular-trace contradiction
target: non-hyperlinear-group
requires:
  - center-chain-common-source-authenticates-native-covariances
  - vanishing-loss-center-chain-authentication-hits-affine-firewall
---

Assume the marked Steinberg group had canonical-trace microstates.  Their
ordinary packet defects `delta_n` tend to zero.  The authentication claim
would produce common-source cuts losing `O(delta_n^alpha)` ambient trace and
native-row errors of the same order, while retaining the relative polar and
mixed-Pauli factorization.  Both quantities tend to zero.  The established
vanishing-loss firewall gives instead the fixed positive lower bound

```text
(1/3-o(1))*sqrt(tau(e)/(128))
```

for the ambient sum of the two row defects.  This contradiction rules out
canonical microstates, so the marked finitely presented Steinberg group is
nonhyperlinear.
