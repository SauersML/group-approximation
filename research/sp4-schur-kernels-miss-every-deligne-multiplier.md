---
rg: 2
id: sp4-schur-kernels-miss-every-deligne-multiplier
kind: claim
title: No nonsingular equation over Sp4(Z) kills a Schur class seen by any Deligne multiplier
distinct_from:
  sp4-schur-kernel-meets-the-deligne-triple-class: that asks for a witness equation; this proves no witness exists, for the mod-three multiplier and for every e mod n.
  deligne-schur-witness-needs-maslov-carrying-packet: that lists necessary conditions (rank-one killed image, Maslov-carrying packets) that a witness would have to meet; this shows the rank-one condition (MP1.2) can never be met.
  real-symplectic-solutions-kill-no-deligne-schur-class: that prunes equations with a real symplectic solution; this covers every nonsingular equation, solvable or not.
  locally-indicable-packets-have-zero-schur-kernel: that prunes coefficient packets by Howie's restriction epimorphism; this uses no packet and applies to torsion packets and every shape.
---

**Theorem.** Let `Gamma = Sp_4(Z)` with integral Maslov class
`e in H^2(Gamma; Z)`. Let `Gamma~`, `Gamma_n` and `e_n = e mod n` be as in
`deligne-schur-witness-needs-maslov-carrying-packet`. Then for every
`w in Gamma * <t>` with `deg_t(w) != 0`:

1. `K_2(Gamma, w)` is finite, so it lies in the finite summand `F` of
   `H_2(Gamma; Z) = Z<h> + F`;
2. `<e, K_2(Gamma, w)> = 0`, and `(e_n)_H(K_2(Gamma, w)) = 0` for every
   `n >= 1`;
3. in particular `alpha_H(K_2(Gamma, w)) = 0` for Deligne's mod-three
   multiplier `alpha = e_3`.

So `sp4-schur-kernel-meets-the-deligne-triple-class` is **false**. Every
Deligne Schur witness would need a rank-one killed image (MP1.2), and no
witness exists.

**Consequences (remarks, not part of the DERIVATION).**
`central-extension-kl-schur-criterion` assumes that `Gamma` injects into
`(Gamma * <t>)/<<w->>`. For `Sp_4(Z)` this holds by
`kervaire-laudenbach-holds-for-hyperlinear`, since `Sp_4(Z)` is residually
finite and hence sofic. That soficity step is not imported as a node here.
Granting it, take `E = Gamma~` (multiplier `e`), `E = Gamma_n` (multiplier
`e_n`) or `E = E_3`. By items 2 and 3 above:

- *Criterion, item 2.* For every nonsingular `w~ in E * <t>`, the central
  subgroup injects into the centralized quotient `(E * <t>)/<<w~, [z, t]>>`.
  So the exact reformulation in the refuted claim, "some nonsingular `w~`
  has `z = 1` in `(E_3 * <t>)/<<w~, [z, t]>>`", fails for every `w~`.
- *Criterion, item 1.* `E` injects into `(E * <t>)/<<w~>>`. So
  Kervaire--Laudenbach holds over `E_3`, over every Deligne cover `Gamma_n`,
  and over `Gamma~`, at every nonsingular equation. This happens even though
  none of these groups is known to be hyperlinear, and `Gamma_n` is not
  residually finite for `n` not dividing 2.

**What dies.** Every route to `deligne-triple-cover-exact-mf-radical`,
`deligne-central-mark-hs-collapse` or `non-hyperlinear-group` through a
Schur-kernel certificate over `Sp_4(Z)`:

- `deligne-central-collapse-via-sp4-schur-kernel`;
- `deligne-opnorm-sectors-empty-via-sp4-schur-kernel`;
- `deligne-rank-collapse-via-sp4-schur-kernel`.

More generally, no nonsingular one-variable equation over a finitely
generated linear group certifies a non-hyperlinear central extension with
torsion-free kernel, or with a multiplier lifted from torsion-free
coefficients (`linear-group-schur-kernels-are-torsion`, Corollary).

DERIVATION
sp4-schur-kernels-miss-every-deligne-multiplier-proof
