---
rg: 2
id: relative-automorphism-fp-host-reflects-base-presentation
kind: claim
title: A finitely presented relative automorphism subgroup containing all base translations forces the base to be finitely presented
distinct_from:
  bffhz-action-image-is-finitely-presented: that concerns the quotient by the evaluation action kernel; this concerns subgroups of the actual relative automorphism group and applies to that quotient only when the action is faithful.
artifacts:
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

Let G be a finitely generated group and 1<=n<infinity. In
A=Aut_G(G*F_n), use the canonical translation embedding

    tau_g(x_1)=x_1*g,  tau_g(x_j)=x_j (j>1),  tau_g|G=id.

If B is a finitely presented subgroup of A containing tau(G), then G is
finitely presented. In particular, finite presentation of A forces finite
presentation of G. Neither simplicity nor an algorithmic hypothesis on G
is needed.

For finitely generated centerless G, the converse for the whole A follows
from BFFHZ Proposition 1.1. Thus A is finitely presented if and only if G
is finitely presented in that scope.

This is specific to the canonical translation embedding in this relative
automorphism group. It says nothing against embedding G in other finitely
presented groups. An arbitrary quotient of A need not satisfy the result.

DERIVATION
[[relative-automorphism-finite-relator-lifting-proof]]
