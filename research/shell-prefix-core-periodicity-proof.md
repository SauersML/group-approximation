---
rg: 2
id: shell-prefix-core-periodicity-proof
kind: route
title: Conjugacy invariance of near index turns a nontrivial prefix core into finitely many periodic rays
target: shell-prefix-core-detects-finite-ray-enumerations
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - finite-ray-shift-envelopes-require-virtually-cyclic-input
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

Every nontrivial subgroup of H is <tau^m> for some m>=1. The core is
normal, so (1) implies (2); any normal subgroup C contained in H is
contained in its core, giving the converse.

If C=<tau^m> is normal, conjugation by q in Q sends its generator
to tau^m or tau^-m. The near index I is conjugacy invariant and
I(tau^m)=m!=0, ruling out the negative choice. Thus C is central.
Commutation of rho_g with tau^m as near permutations says exactly

    rho_g(n+m)=rho_g(n)+m eventually.

Conversely this condition for every g, together with commutation of
tau and tau^m, makes C central in the generated group Q.

For an actual permutation satisfying the displayed condition, each
residue ray modulo m is eventually sent to a residue ray by translation
of its ray coordinate. Two source rays cannot have the same target
ray, since their image tails would intersect and violate injectivity.
Every target ray is reached by surjectivity. Thus rho(P) is a subgroup
of the eventually m-periodic permutation group. It has the even
integers as a free orbit. The regular-orbit classification in the
required claim therefore makes P virtually cyclic. This argument
does not require finite generation of P.

For the converse choose an infinite cyclic normal subgroup <t> of
finite index d in P and coset representatives r_i, 0<=i<d. Use the
following zero-based version of the finite-ray enumeration:

    nu(t^k*r_i)=2d*k+i                  for k>=0,
    nu(t^k*r_i)=2d*(-k-1)+d+i           for k<0.

For g in P write g*t*g^-1=t^epsilon, epsilon in {1,-1}, and
g*r_i=t^(c_i)*r_(sigma(i)). Left multiplication sends k to
epsilon*k+c_i, so on the positive and negative tails it permutes
the 2d rays and translates their ray coordinates. Consequently
the transported regular action is eventually 2d-periodic.
Putting it on the even integers and fixing the odd integers makes
rho_g eventually 4d-periodic. Take m=4d. This proves existence
of the desired enumeration and central C.
