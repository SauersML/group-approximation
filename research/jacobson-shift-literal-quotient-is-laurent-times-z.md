---
rg: 2
id: jacobson-shift-literal-quotient-is-laurent-times-z
kind: claim
title: The literal stable-letter quotient is the Laurent special linear group times the integers
distinct_from:
  jacobson-shift-head-generates-normal-finitary-kernel: that presents the abstract quotient as Lambda times Z without identifying Lambda; this computes the literal quotient and identifies the precise kernel of the abstract-to-literal map.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that computes the symbol kernel in the full unilateral ring group; this concerns the separately specified bilateral stable-letter presentation.
artifacts:
  - research/artifacts/jacobson-stable-letter-laurent-quotient-and-local-inner-action-2026-09-08.md
---

Let `Gamma=Theta_shift`, let `L` be its proved normal finitary
subgroup, and let `pi` be the literal bilateral action. Put
`R=F_2[z,z^(-1)]`. Then

```text
pi(Gamma)/pi(L) ~= SL_3(R) x Z.
```

For the established quotient `Gamma/L=Lambda x Z`, the induced
symbol map is `(lambda,k)|->(kappa(lambda),k)`, with the explicitly
specified surjection `kappa:Lambda->SL_3(R)`. Restriction of the
quotient map gives

```text
ker(pi) ~= ker(kappa),
[ker(pi),t]=1.
```

The later affine countermodel in
`jacobson-laurent-kernel-surjects-natural-affine-module` proves
that `ker(kappa)` and `ker(pi)` are infinite and noncentral.
In particular this specified Laurent map is not an isomorphism.
The unrestricted marked matrix gap remains unresolved.

DERIVATION
jacobson-shift-positive-symbol-and-kernel-proof
