---
rg: 2
id: virtually-fuchsian-coefficients-have-zero-schur-kernel
kind: claim
title: Coefficient packets that are hyperlinear and virtually projectively visible, such as virtually Fuchsian groups with torsion, have zero Schur kernel
distinct_from:
  projective-unitary-classes-vanish-on-schur-kernel: that shows projective unitary multipliers of the coefficient group vanish on the Schur kernel, and so kills the kernel when those multipliers separate H_2 (finite groups); this proves that finite-dimensional multipliers do separate H_2 for every group that is virtually a torsion-free Fuchsian group, by induction from a finite-index subgroup, so infinite packets with H_2(-; Q) = Q and torsion are covered.
  amenable-coefficients-have-zero-schur-kernel: that removes coefficient subgroups whose twisted algebras are Connes-embeddable, such as amenable ones; this removes non-amenable packets such as cocompact triangle groups and arithmetic quaternionic unit groups.
  deligne-schur-witness-needs-maslov-carrying-packet: that prunes packets over Sp_4(Z) by the Maslov class through rational parabolics and Lie subgroup windings; this kills the whole Schur kernel for any packet that is virtually a surface group, including Maslov-carrying packets with a compact commutant that survive every criterion there.
  aspherical-adjunction-has-zero-schur-kernel: that needs an aspherical one-relator adjunction; this places no condition on the equation beyond nonsingularity and constrains only the coefficient group.
artifacts:
  - research/artifacts/sp4-schur-zariski-closure-packets-2026-09-17.md
  - experiments/sp4-schur-zariski-closure-packets-2026-09-17/verify.py
  - experiments/sp4-schur-zariski-closure-packets-2026-09-17/output.txt
---

**Definition.** A group `S` is *projectively visible* if every element of
`Hom(H_2(S; Z), Q/Z) <= Hom(H_2(S; Z), U(1)) = H^2(S; U(1))` is the multiplier
class of some homomorphism `S -> PU(n)`, `n` finite.

**Claim.** Let `Q` be a group and `w in Q * <t>` with nonzero exponent sum in
`t`. Let `B <= Q` contain the coefficients of `w`, and assume:

1. `B` is countable and hyperlinear;
2. some finite-index subgroup `S <= B` is projectively visible.

Then `K_2(B, w) = 0` and `K_2(Q, w) = 0`.

**Visible groups.** Finite groups are projectively visible. So is every
torsion-free discrete subgroup of `PSL_2(R)`:

- with noncompact quotient, `H_2 = 0`;
- with closed quotient of genus `g >= 2`, the clock-shift map `a_1 -> X_q^k`,
  `b_1 -> Y_q`, other generators `-> 1`, realizes the class `k/q`.

Consequently the claim holds whenever `B` is a finitely generated group that is
virtually a torsion-free Fuchsian group. Selberg's lemma makes this include
every finitely generated discrete subgroup of `SL_2(R)`, and every
finite-by-Fuchsian group. Hyperlinearity is automatic there, since these groups
are residually finite.

**New reach.** The locally indicable packet theorem (Howie) needs local
indicability, possibly modulo a finite normal subgroup of order prime to `p`.
P1 of `deligne-schur-witness-needs-maslov-carrying-packet` needs
`H_2(-; Q) = 0`. Forester--Rourke needs torsion-freeness. Cocompact triangle
groups and arithmetic unit groups of indefinite quaternion algebras fail all of
these conditions and are covered here. The explicit packet `Lambda^1 <= Sp_4(Z)`
of the artifact, Section 4, is an example.

DERIVATION
virtually-fuchsian-schur-kernel-proof
