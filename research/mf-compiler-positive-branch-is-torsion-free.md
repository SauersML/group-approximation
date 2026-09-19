---
rg: 2
id: mf-compiler-positive-branch-is-torsion-free
kind: claim
title: Every positive-branch output of the MF-safe finite-presentation compiler is torsion-free
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
distinct_from:
  mf-compiler-positive-branch-is-hyperlinear: that asks for an analytic property of the same groups, quasidiagonality of a trace; this is an elementary structural fact, proved from the torsion theorems for amalgams and HNN extensions, and it is what makes the finite-presentation Rice criterion nonvacuous.
  mf-safe-finite-presentation-compiler: that is the compiler and its MF branch; this records a further property of the same positive branch.
---

ESTABLISHED.  Let `R_e` be the finitely presented rope produced by
[[mf-safe-finite-presentation-compiler]] on an input `e` with infinite
domain (the branch on which the switch group collapses).  Then `R_e` is
torsion-free.  The statement does not depend on the seed: on the `INF`
branch the compiler's output is seed-independent.

**Proof.**  Read the construction bottom-up and use two classical facts:
in an amalgamated free product every element of finite order is conjugate
into a factor (Serre, *Trees*, I.4.3), and in an HNN extension every
element of finite order is conjugate into the base (Britton's lemma, or
Serre again through the Bass--Serre tree).

* `F`, `F(X_e)` and the free factors of the graph witness are free, hence
  torsion-free.
* `K_e^0 = F x F(X_e) x F(X_e)` and `K^g = F x P` with `P = F(x_1,y) x
  F(x_2,t)` are finite direct products of free groups; a direct product of
  torsion-free groups is torsion-free.  So `K_e = K_e^0 x K^g` is
  torsion-free, and so is its subgroup `L_e` (which contains the
  Mikhailova subgroup `M_e <= F(X_e) x F(X_e)`).
* `Gamma_e = <K_e, v | [v, L_e] = 1> = K_e *_{L_e} (L_e x Z)` is an
  amalgamated free product of the torsion-free groups `K_e` and
  `L_e x Z`, hence torsion-free.
* On `INF` the value of the two-generator bridge is `Q_e = B3(1) =
  (F_oo x F_oo) x| Z`, which embeds in `F_2 x F_2` and is therefore
  torsion-free ([[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]).
* `R_e` is an HNN extension of the base `Gamma_e x Q_e` along the
  subgroup `S_e`, so every torsion element of `R_e` is conjugate into
  that base, which is a direct product of two torsion-free groups.

Hence `R_e` has no nontrivial element of finite order.
