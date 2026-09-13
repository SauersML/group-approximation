---
rg: 2
id: amenable-t-shape-adjunctions-kill-no-schur-class
kind: claim
title: An amenable-shape equation whose coefficients generate a torsion-free subgroup kills no Schur multiplier class
distinct_from:
  aspherical-adjunction-has-zero-schur-kernel: that takes asphericity of the cellular model as a hypothesis; this proves that hypothesis whenever the coefficients lie in a torsion-free subgroup, for any ambient group, torsion allowed.
  amenable-coefficients-have-zero-schur-kernel: that needs Connes-embeddable twisted algebras of the coefficient subgroup; this uses no approximation property, only torsion-freeness of the coefficient subgroup and an amenable t-shape.
  some-nonsingular-equation-has-nonzero-schur-kernel: that asks for one Schur kill anywhere; this removes every equation with torsion-free coefficient subgroup and amenable t-shape from that search.
artifacts:
  - research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md
---

Let `Q` be any group and `w in Q * <t>` nonsingular. Suppose the coefficients of
`w` lie in a torsion-free subgroup `B <= Q`, and the `t`-shape of the cyclically
reduced form of `w` is amenable. In particular, `deg_t(w) = ±1` qualifies.
Then:

1. `Q -> (Q * <t>)/<<w>>` is injective;
2. `(K(Q,1) v S^1) cup_w e^2` is aspherical;
3. `K_2(Q, w) = ker( H_2(Q; Z) -> H_2((Q * <t>)/<<w>>; Z) ) = 0`.

**Consequences.**

* **Schur-kill search.** Any witness for
  `some-nonsingular-equation-has-nonzero-schur-kernel` must have torsion in
  every subgroup containing its coefficients, or a non-amenable `t`-shape
  (e.g. a proper-power shape, or a root with at least two clumps).
* **Deligne target.** For `sp4-schur-kernel-meets-the-deligne-triple-class`,
  coefficient packets inside a torsion-free subgroup of `Sp_4(Z)` are dead at
  every amenable shape. The principal congruence subgroups `Gamma(N)`,
  `N >= 3`, are torsion-free; that is a standard fact, not re-read here.
* **Degree scope.** Over torsion-free coefficient groups, item 1 already
  holds at every amenable shape, including degrees `|m| >= 2`. So the
  falsification instrument recorded on `klyachko-kl-holds-for-torsion-free`
  survives only at non-amenable shapes, not at all of `|m| >= 2`.

No priority is claimed. The deduction is two lemmas of Bogley--Edjvet--Williams
applied to the Forester--Rourke theorem.
