---
rg: 2
id: free-shift-finite-relators-and-prefix-rigidity-proof
kind: route
title: Finite certificates would preserve a finite presentation under a changed enumeration and force impossible marked rigidity
target: free-shift-shell-envelopes-are-not-finitely-presented
requires:
  - free-shift-shell-relations-are-finitely-certified
  - cantor-prefix-subgroup-detects-every-normal-kernel
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Suppose E_nu is finitely presented. Transfer a finite presentation
to the finite generating set consisting of fixed generators of V
and hat(S). This can be done by finitely many Tietze transformations.
Let w_1,...,w_r be its finite list of defining relators.

For each w_i the required finite-certificate claim gives a finite
restriction sigma_i of nu preserving that relation in E_mu for
every extension mu. Let sigma be their union, also prescribing the
value of nu(1_P). Choose two integers outside the finite range of
sigma, and let pi interchange them and fix the other integers.
Put mu=pi*nu. Then mu extends sigma, mu(1_P)=nu(1_P), and mu!=nu.

All relators w_i hold in E_mu. Thus their presentation gives a
surjective homomorphism

    phi:E_nu->E_mu,
    phi(v)=v for v in V,
    phi(hat_nu(g))=hat_mu(g) for g in S.

The normal-kernel detector for an actual Cantor homeomorphism group
containing V says that a homomorphism injective on V is injective
on the whole group. Since phi restricts to the identity on V, its
kernel is trivial.
Hence phi is an isomorphism with these specified markings.

For n>=0 let v_n in V flip the first suffix bit within the shell
C_n and fix its complement. Its support is exactly C_n, so these
involutions are pairwise distinct. For every input generator g,

    hat_nu(g)*v_n*hat_nu(g)^-1 = v_(rho_nu,g(n)).

Apply phi. It fixes EVERY element of V, including all v_n, and
the same identity for mu gives rho_nu,g(n)=rho_mu,g(n) for all n.
The generator permutations therefore agree, as do their products
for all g in P. Let n_0=nu(1_P)=mu(1_P). Evaluating at the even
index 2*n_0 gives

    2*nu(g)=rho_nu,g(2*n_0)=rho_mu,g(2*n_0)=2*mu(g).

Thus nu=mu, a contradiction. No computational assumption was used.

The finite swap changes only finitely many enumeration values;
nevertheless the full marked action detects it. The contradiction
uses finite determination of the proposed relators, not any claim
that nearby enumerations must give distinct abstract groups.
