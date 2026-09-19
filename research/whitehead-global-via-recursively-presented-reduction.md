---
rg: 2
id: whitehead-global-via-recursively-presented-reduction
kind: route
title: Transplant the finite multiplication table, then quotient by the torsion-free radical
target: whitehead-vanishing-torsion-free
requires: [whitehead-vanishing-recursively-presented-torsion-free, whitehead-class-supported-on-finitely-generated-subgroup, torsion-free-universal-quotient-recursively-presented]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Let `G` be torsion-free and `x` in `Wh(G)`, represented by `A` in `GL_n(ZG)`
with `B = A^-1`.  Let `S` be the finite set of group elements occurring in
the entries of `A` and `B` (this is the finite-support claim), and let
`T = {1} u S u S.S`.

Let `P` be the group with one generator `x_t` for each `t` in `T`, and the
finitely many relations

    x_1 = 1,     x_s x_s' = x_{ss'}    for all (s,s') in S x S.

`P` is finitely presented and `phi : P -> G`, `x_t |-> t`, is a homomorphism,
every imposed relation being true in `G`.

Let `Ahat`, `Bhat` in `M_n(ZP)` replace each coefficient `s` by `x_s`.  In
`ZG` the entry `(AB)_{ik}` is a sum of terms supported at products `ss'`,
like terms combining exactly when the products agree in `G`; in `ZP` the
relations put the same sum at the labels `ss'`, combining under exactly the
same condition.  The coefficient collections are therefore identical, so
`Ahat Bhat = delta_{ik} x_1 = I_n`, and symmetrically `Bhat Ahat = I_n`.
Thus `Ahat` is in `GL_n(ZP)`.

Let `Ptf = P/Tor_oo(P)`, which is torsion-free, finitely generated (a
quotient of `P`) and recursively presented, by
`torsion-free-universal-quotient-recursively-presented`.  Since `G` is
torsion-free, the universal property factors `phi` as
`P -> Ptf ->^psi G`.  Let `Atilde` be the image of `Ahat` in `M_n(Z Ptf)`;
it is invertible by functoriality, and `psi_*[Atilde] = [A] = x`.

By hypothesis `Wh(Ptf) = 0`, so `[Atilde] = 0` and hence `x = 0`.

## Why this is the sharp form

The obvious reduction stops at finitely generated groups, of which there are
continuum many while only countably many are recursively presented; the step
above goes further, and does so without any inequation apparatus.  Sets of
nontrivial differences are needed only when the target is a finitely
*presented* overgroup, where the comparison homomorphism points away from
`G` and faithfulness must be purchased
(`finite-torsion-free-pattern-realizable-finitely-presented`).  Here the
comparison map `psi : Ptf -> G` points back at `G`, so functoriality alone
carries the vanishing home.

This is the route that makes the finitely-presented lane's missing step
`whitehead-injective-torsion-free-embedding` *sufficient* rather than merely
necessary: that statement is quantified over exactly the class this route
reduces to.
