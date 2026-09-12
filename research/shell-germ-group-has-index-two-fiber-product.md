---
rg: 2
id: shell-germ-group-has-index-two-fiber-product
kind: claim
title: The universal shell germ group is an index-two extension of a symmetric fiber product over Z
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

Let P be countably infinite, with enumeration nu:P->N. Let lambda_g
be its transported regular permutation of all N, let s:n->n+1 be
the cofinite shift, and define the near permutation group

    R_nu=<lambda(P),s>,       eta=near index:R_nu->Z.

For the shell isotropy germ group Q=<rho(P),tau>, where rho acts on
evens and fixes odds, the subgroup preserving parity near infinity
has index two and identifies faithfully with

    F_nu=R_nu x_Z R_nu
        ={(a,b) in R_nu x R_nu: eta(a)=eta(b)}.

Consequently Q is finitely presented if and only if F_nu is. If P
is finitely generated and these equivalent properties hold, then
R_nu is finitely presented as well. Combining this with the simple
neighborhood-kernel test gives

    A_1 finitely presented ==> F_nu finitely presented
                           ==> R_nu finitely presented.

There is also an exact finite-relator test when P is finitely generated
by S and R_nu is finitely presented. Form T=R_nu *_<s> R_nu, identifying
the two shifts, and write lambda_g^(1),lambda_g^(2) for the input
elements in its two factors. Then F_nu is finitely presented if and
only if some integer B>=0 has the following property: every relator

    [lambda_g^(1), s^k*lambda_h^(2)*s^-k],   g,h in S, k in Z,

lies in the normal closure in T of the finitely many such relators
with |k|<=B. This requires a proof for all k, not verification of
a finite interval alone.

The first implication is not asserted reversible. No finite presentation
of F_nu or R_nu is claimed for arbitrary P or arbitrary nu. These are
near permutation groups; finitary permutations have been quotiented
out, and they are not the earlier Mallery--Zaremsky permutation envelope.
