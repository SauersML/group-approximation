---
rg: 2
id: kl-holds-over-central-extensions-of-torsion-free-groups
kind: claim
title: Amenable-shape equations inject every central extension of a torsion-free group
distinct_from:
  klyachko-kl-holds-for-torsion-free: that needs torsion-free coefficients; this allows arbitrary central torsion, such as covers of torsion-free lattices that are not residually finite.
  central-extension-kl-schur-criterion: that is a criterion whose Schur hypothesis must be checked equation by equation; this discharges the hypothesis for every amenable-shape equation over a torsion-free quotient.
  kervaire-laudenbach-holds-for-hyperlinear: that uses an approximation property of the coefficient group; this uses none, and covers groups whose hyperlinearity is open.
artifacts:
  - research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md
---

Let `1 -> Z -> E -> Q -> 1` be a central extension with `Q` torsion-free. Let
`w in E * <t>` be nonsingular, with image `w-` in `Q * <t>`. Suppose the
cyclically reduced form of `w-` has an amenable `t`-shape; exponent sum `±1` is
enough, since the exponent sum does not change. Then
`E -> (E * <t>)/<<w>>` is injective.

**Corollary.** Let `E` be a group whose elements of finite order are all
central. Every unimodular equation over `E` injects `E`, and so does every
nonsingular equation of amenable `t`-shape after reduction modulo the torsion.
The finite-order elements commute and are central, so they form a central
subgroup `T`. `E/T` is torsion-free, because `x^n in T` forces `x` to have
finite order.

**Example.** Take a torsion-free finite-index subgroup `Gamma <= Sp_4(Z)` and
its preimage `E_Gamma` in Deligne's triple cover `E_3`. `E_Gamma` is a central
extension of `Gamma` by `Z/3`, so it satisfies unimodular Kervaire--Laudenbach.
It is not residually finite: every finite-index subgroup of `E_3` contains the
central mark, as main records from Deligne's theorem (second hand here). Its
hyperlinearity is open on main.

No priority is claimed; the sources read state only the torsion-free case.
