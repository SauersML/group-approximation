---
rg: 2
id: compression-wreath-five-radicals-coincide
kind: claim
title: One kernel for five approximation theories in the compression wreath family
distinct_from:
  wreath-compression-mf-radical: That claim computes the MF radical of the family as the telescope kernel; this one proves the same subgroup is simultaneously four further residuals (finite, finite-dimensional unitary, all-fields linear, Bohr) and therefore a single universal visible quotient.
  matricial-stability-identifies-radicals: That identifies Rad_MF with Rad_fd under a matricial-stability hypothesis on the group; this computes five residuals of a concrete family with no stability hypothesis, and includes the finite, linear, and Bohr kernels that stability says nothing about.
  corona-hs-radical-is-finite-residual: That computes the 2-norm-invisible set of the literal commuting-lamp quotient and equates it with the finite residual there; this is the operator-norm radical of the compression wreath family and adds the linear and Bohr layers.
  commuting-lamp-mf-radical-is-level-even: That open claim asks for the exact operator-norm radical of the marked quotient `W/<zeta>`; this concerns the plain compression wreath products `K^(G/Gamma) x| G`, whose radical is already established.
  universal-mf-quotient: That is the generic existence of a largest MF quotient; this identifies one explicit quotient as universal for five target classes at once.
artifacts:
  - GroupApproximation/Algebra/VisibleQuotient.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Sofic/LinearResidual.lean
  - GroupApproximation/Algebra/FiniteResidual.lean
---

For the concrete doubling family `W_K = K^(G*/Gamma*) x| G*` with `K` a
nontrivial finite group, write `R_K` for the telescope kernel and
`P_K = K_ab^(Z) x| G*` for the quotient.  Then

    R_K = Rad_MF(W_K) = Rad_fd(W_K) = Rad_lin(W_K)
        = Rad_Bohr(W_K) = Res_fin(W_K),

where `Rad_lin` intersects the kernels of all finite-dimensional linear
representations over **all** fields and `Rad_Bohr` intersects the kernels of
all homomorphisms into compact groups.

Equivalently, in factorization form: for every target `T` that is a finite
group, a residually finite group, a countable MF group, `GL_d(F)` for any
field `F`, `U(d)`, a compact Hausdorff group, or the unitary group of a norm
matrix corona, precomposition with `W_K -> P_K` is a **bijection**

    Hom(P_K, T)  ->  Hom(W_K, T).

So `P_K` is the universal visible quotient for all of these approximation
theories at once, and `R_K` is exactly the intersection of all finite-index
subgroups of `W_K`.

Two immediate consequences: `W_K` is not linear over any field and not even
virtually linear, and `W_K` is not maximally almost periodic.
