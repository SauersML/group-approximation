---
rg: 2
id: deligne-homogeneous-bundle-models-die-over-every-lattice
kind: claim
title: No lattice of Sp_4(R), cocompact or not, carries a Lie-homogeneous circle-bundle model of Deligne's triple cover, so no compact locally symmetric Sp_4 space gives a homogeneous continuous untwisting
distinct_from:
  deligne-homogeneous-bundle-models-die-at-lattice-residual: that proves the same non-existence unconditionally only for lattices commensurable with a conjugate of Sp_4(Z), all non-uniform, and for other lattices under the congruence subgroup property as an explicit hypothesis; this removes the hypothesis, so it covers every cocompact lattice, the case that matters for (U).
  deligne-third-floor-failure-is-continuous-untwisting: that reduces floor failure to a finitely approximable space with a continuous untwisting and kills discrete-phase, Bernoulli-profinite and local-rule spaces; this shows that no compact homogeneous space Sp_4(R)/Lambda_0 carries an untwisting of the algebraic kind at all.
  deligne-covers-of-sp2g-z-have-finite-residual-2z: that is Deligne's residual for Sp_2g(Z); this uses Deligne's theorem, in Stover's form, for every arithmetic group of type C_2 over a totally real field, most of them anisotropic.
  central-extension-untwisting-over-boundaries: that obstructs untwisting over boundary actions through stabilizers; here every stabilizer is trivial, and the obstruction is the residual of the lattice that defines the space.
  sp4-forms-have-central-congruence-kernel: that is the congruence subgroup property for k-forms of Sp_4, an input here; this is its consequence for circle-bundle models of E_3.
---

**ESTABLISHED** (`deligne-homogeneous-bundle-models-die-over-every-lattice-proof`). Unreviewed.

## Statement

Use the notation of `deligne-homogeneous-bundle-models-die-at-lattice-residual`: `G = Sp_4(R)`, `G~` its
universal cover, `L_t = (G~ x T)/{(z^k, -kt)}`, and a homogeneous model `(t, Lambda, rho~)` of
`E_3 = Gamma~/<z^3>`.

**Theorem.** For every lattice `Lambda_0` of `Sp_4(R)`, uniform or not, arithmetic over any totally real field,
there is no homogeneous model `(t, Lambda, rho~)` whose `Lambda` has image `Lambda_0`. Only `Lambda cap T`
finite is needed, not discreteness of `Lambda`.

**Corollary (compact case).** Let `K = Sp_4(R)/Lambda_0` be compact, and let `t in T` and `Lambda <= L_t` be
discrete over `Lambda_0`. Then no homomorphism `rho~ : E_3 -> L_t` lifting `Gamma <= Sp_4(R)` has
`rho~(z) not in Lambda`. So `E_3` never acts by left translation on the circle bundle `L_t/Lambda -> K` over the
`Gamma`-action on `K` with `z` rotating the fibres nontrivially. In particular, none of the continuous untwistings of (U) in
`deligne-third-floor-failure-is-continuous-untwisting` is homogeneous: the untwisted space of a refutation of
(NFA) is never `L_t/Lambda` over a compact locally symmetric `Sp_4` space.

## What this kills

**Named invariant.** `Res_fin(Lambda_(0,n))` for `n in {3, 6}`, the finite residual of the `n`-fold cover of the
lattice that defines the space. It is nontrivial for every lattice `Lambda_0` of `Sp_4(R)`. This follows from
Deligne's theorem (in Stover's Theorem 3.3), since the congruence subgroup property holds for every `k`-form of
`Sp_4` (`sp4-forms-have-central-congruence-kernel`).

**The class killed.** The class is refutations of the third floor, and of (NFA), whose untwisted space is a
homogeneous circle bundle over a locally symmetric space `Sp_4(R)/Lambda_0` for an arbitrary lattice
`Lambda_0`. The approximating finite `Gamma`-sets would come from the congruence quotients of `Lambda_0`. The
w20 node proved this kill only over the non-uniform commensurability class of `Sp_4(Z)`, which excludes no
compact `K`, and conditionally elsewhere. The compact case is now unconditional.

**Where it dies.** It dies at the lattice-splitting step, exactly as in the w20 node. A section of `Lambda` over
`Lambda_0` is a character `f` of `Lambda_0~` with `f(z)` of order `n` in `{3, 6}`. That character linearizes
`Lambda_(0,n)` into `Sp_4(R) x U(1)`, and Deligne's residual forbids it.

**Belief change.** Before this, the compact homogeneous quotients were the one natural connected phase space
that (C2) leaves open and that no node excluded unconditionally. The only obstruction was anisotropic CSP. That
obstruction is a theorem, and it holds uniformly over every totally real field and every form. So a refutation
of (NFA) has to use a phase space that is not Lie-homogeneous over `Sp_4(R)`, for example the connected space
`K''/<z>` from step 6 of the (U) node, or a non-algebraic bundle.

## What it does not do

- It does not decide the third floor or (NFA). It removes one class of candidate counterexamples, and the
  flagship stays OPEN.
- The remaining restrictions of the w20 node still apply. Only circle extensions `L` with `L/T = Sp_4(R)` are
  treated, and `rho~` must lift the standard inclusion `Gamma <= Sp_4(R)`. Non-homogeneous systems, for
  instance affine systems over Cantor bases, or bundles whose transition data are not algebraic, are untouched.
- Deligne's theorem enters only through Stover's Theorem 3.3, as imported in the w20 proof. No new use of
  metaplectic kernels is made.

## Attempts

- 2026-09-20 (swarm-0917-w21-w21-deligne-follow), Riemann-Roch integrality, **dead as an obstruction**. This
  was a topological substitute for CSP on compact quotients.
  - Idea: a homogeneous model over a torsion-free cocompact `Lambda_0` would make a fractional power `K^(1/3)`
    or `K^(2/3)` of the canonical bundle of the compact Siegel threefold `X = Lambda_0 \ H_2` exist as an
    automorphic line bundle. Here `K_X = L_1^3`, and the compact dual is the quadric `Q^3` with `K = O(-3)`.
  - Holomorphic Euler characteristics must then be integers. By Hirzebruch proportionality,
    `chi(X, L_1^s) = r(X) P(-s)` up to sign, with `P(s) = (s+1)(s+2)(2s+3)/6`, the Hilbert polynomial of `Q^3`,
    and `r(X) = +- chi(X, O_X)`.
  - `P(1/3) = 154/81` and `P(2/3) = 260/81`, so the only condition is `81 | r(X)`.
  - `r` is multiplicative in the degree of finite covers, so the condition holds on every cover of degree
    divisible by 81 and gives no obstruction on deep congruence covers. Hence characteristic-number arguments
    cannot replace the arithmetic input.
  - Consistently, the obstruction that does work, `Res_fin(Lambda_(0,n)) != 1`, is not visible on any single
    finite cover.
- 2026-09-20 (same worker), the congruence subgroup property for the anisotropic forms, **succeeded**. It is
  imported from Rapinchuk 1992, Theorem 1, which covers `C_n (n ≥ 2)` with `rang_S ≥ 2` and has no isotropy
  hypothesis. This gives the ESTABLISHED status above, through `sp4-forms-have-central-congruence-kernel`.
