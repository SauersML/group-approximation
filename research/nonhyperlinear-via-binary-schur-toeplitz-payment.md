---
rg: 2
id: nonhyperlinear-via-binary-schur-toeplitz-payment
kind: route
title: Use the binary Schur child shift and pay one of its two retained branches
target: non-hyperlinear-group
requires:
  - binary-schur-child-toeplitz-self-embedding
  - binary-schur-toeplitz-one-branch-hs-payment
---

Form `(Hsharp,w)` from `(BHP1)`.  The coefficient algebra has a faithful
infinite unilateral-shift model, `Sigma` is injective, and Britton normal form
therefore keeps the base root `w=x_12(P)` nontrivial in the ascending HNN
group.  Every exact finite-dimensional coefficient representation kills `P`
by direct finiteness.

If `Hsharp` were hyperlinear, canonical-delta microstates would keep the
nonidentity order-`p` word `w` a fixed positive normalized-HS distance from
the identity.  The one-branch payment `(BHP2)` instead forces that distance to
zero.  This contradiction makes `Hsharp` nonhyperlinear.  Higman's effective
embedding theorem may then be applied if a finitely presented overgroup is
desired.

Unlike the one-step Schur--Toeplitz route, the factor two is present in the
coefficient endomorphism itself.  The only open input is the finite-dimensional
payment for one named corrected-child branch.
