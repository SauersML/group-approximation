---
rg: 2
id: shell-finite-perturbation-and-noncomputability-proof
kind: route
title: Realize finite relabelings inside V and use computability extraction to exclude the remaining enumerations
target: shell-finite-prefix-cannot-certify-presentation
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - shell-recursive-presentations-compute-enumerations
  - virtually-cyclic-inputs-have-fp-shell-stabilizers
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

Suppose nu'=sigma*nu, with sigma a finitary permutation of N.
Let pi act on even integers by pi(2n)=2*sigma(n) and fix odds.
Its shell lift hat(pi) exchanges only finitely many entire shells
by suffix-preserving prefix maps. It belongs to V and fixes p.
The transported regular actions satisfy

    rho'_g=pi*rho_g*pi^-1,
    hat(g)'=hat(pi)*hat(g)*hat(pi)^-1.

Since hat(pi) belongs to V<=E_nu,

    E_(nu')=hat(pi)*E_nu*hat(pi)^-1=E_nu.

Singularities are measured against the same V and the designated
points are unchanged, so the same is true of every S(M,M').

For a virtually cyclic input, start with the finite-ray enumeration
nu_0 from the positive control. Given a finite injective prescription
alpha on a finite set D<=P, extend the finite assignment
nu_0(g) -> alpha(g), g in D, to a finitary permutation sigma of N.
This extension exists by completing a bijection on the finite union
nu_0(D) union alpha(D) and fixing its complement. Then sigma*nu_0
extends alpha and gives the very same E and stabilizers as nu_0,
so they are finitely presented.

The set of extensions of alpha has cardinality continuum: pair up
infinitely many unassigned domain and range values and choose
independently whether to interchange each pair. Only countably many
enumerations can be computed by algorithms on words in a fixed finite
generating set of P. Choose a noncomputable extension. The extraction
claim rules out any recursive presentation of its E or A_1.

For either group, that extraction also shows that its recursively
presentable locus, and hence its finite-presentation locus, is
countable. The positive construction makes the latter dense. Each
singleton enumeration is closed with empty interior in the topology
of finite agreement: any finite prescription leaves infinitely many
values free. Thus a countable locus is meagre, and its complement
is comeagre. The noncomputable choices in every finite-agreement
neighborhood additionally show the claimed density directly.
