---
rg: 2
id: schur-kernel-shrinks-along-consequences-and-hosts
kind: claim
title: The Schur kernel of an equation shrinks along its consequences and dies in the second homology of every solving host
distinct_from:
  aspherical-adjunction-has-zero-schur-kernel: that proves one equation's kernel is zero from asphericity of its own cellular model; this compares the kernels of an equation and of its consequences, and spreads the zero kernel to every nonsingular consequence of an aspherical equation.
  amenable-t-shape-adjunctions-kill-no-schur-class: that prunes equations with torsion-free coefficients and amenable t-shape; this prunes every nonsingular consequence of such an equation, whose coefficients and shape can be arbitrary.
  real-symplectic-solutions-kill-no-deligne-schur-class: that pulls back a central extension of a host to control one multiplier; this bounds the whole Schur kernel by the kernel on second homology of any host where the equation is solvable, and needs no central extension.
  schur-kernel-lies-in-hyperlinear-radical: that places multiplier values of killed classes in hyperlinear radicals of central extensions; this is an elementary comparison between kernels of related adjunctions and hosts.
artifacts:
  - research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md
---

**Setting.** For a group `Q` and a nonsingular `w in Q * <t>`
(`deg_t w != 0`), put `A_w = (Q * <t>)/<<w>>`, `q : Q -> A_w`, and
`K_2(Q, w) = ker(q_* : H_2(Q; Z) -> H_2(A_w; Z))`. For `phi : Q -> L`,
`w_phi in L * <t>` is `w` with `phi` applied to its coefficients.

**(CM1) Consequence monotonicity.** If `w in <<u>>` in `Q * <t>`, then
`deg_t w` is a multiple of `deg_t u` and `K_2(Q, w) <= K_2(Q, u)`. So a
nonsingular `w` has only nonsingular normal-closure roots `u`. If `w` kills
a class, or kills a class detected by some multiplier, then so does every
such `u`.

**(CM2) Pruning spreads to consequences.** Suppose
`(K(Q,1) v S^1) cup_u e^2` is aspherical, or the coefficients of `u` lie in
a torsion-free subgroup and the reduced `t`-shape of `u` is amenable. Then
`K_2(Q, v) = 0` for every nonsingular `v in <<u>>`. This includes every
proper power `u^k` (`|k| >= 2`) and every product of conjugates of
`u^{±1}` with nonzero exponent sum, whatever their coefficients and shapes.

**(CM3) Host bound.** If `w_phi(l) = 1` for some `l in L`, then
`K_2(Q, w) <= ker(phi_* : H_2(Q; Z) -> H_2(L; Z))`. In particular an
equation with a solution in `Q` itself has zero Schur kernel.

**(CM4) Rationally injective hosts.** If `P` is an amalgam `Q *_C D` or an
HNN extension of `Q` along `C` with `H_2(C; Q) = 0`, then
`H_2(Q; Q) -> H_2(P; Q)` is injective. The same holds for finite iterates and
directed unions, for example iterated root adjunctions `Q *_{c = s^k} <s>`.
With (CM3), a solution in such a host forces `K_2(Q, w)` to be torsion.

**Why it matters.** (CM1) says the search for a Schur kill may always
replace an equation by any of its normal-closure roots, and (CM2) removes
whole normal closures from the search at once. (CM3)--(CM4) turn solvability
in a host into a homological bound without any central extension.

**Scope.** No priority is claimed; the arguments are elementary
(Mayer--Vietoris, functoriality). Full proofs are in Section 1 of the
artifact.

DERIVATION
schur-kernel-consequence-host-proof
