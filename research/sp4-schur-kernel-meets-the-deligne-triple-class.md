---
rg: 2
id: sp4-schur-kernel-meets-the-deligne-triple-class
kind: claim
refuted_by: sp4-schur-kernels-miss-every-deligne-multiplier
title: A nonsingular equation over Sp4(Z) kills a Schur class detected by Deligne's mod-three multiplier
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is an operator-norm emptiness statement about the two nontrivial Maslov sectors; this asks for an algebraic one-variable equation over Sp4(Z) whose adjunction kills a second-homology class on which the mod-three multiplier is nonzero.
  maslov-mod3-projective-defect-gap: that is a uniform analytic defect gap for alpha-projective almost representations; this is a finite algebraic certificate that implies the central collapse without estimating any defect.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
  - research/artifacts/sp4-schur-li-packets-2026-09-17.md
---

**OPEN.** Let `alpha` be the multiplier of Deligne's triple cover
`1 -> <z> = Z/3 -> E_3 -> Sp_4(Z) -> 1`, with evaluation
`alpha_H : H_2(Sp_4(Z); Z) -> Z/3`. There is `w in Sp_4(Z) * <t>` with
`deg_t(w) != 0` and

    alpha_H( ker( H_2(Sp_4(Z)) -> H_2((Sp_4(Z) * <t>)/<<w>>) ) ) != 0.

By `schur-kernel-lies-in-hyperlinear-radical` this gives `z in Rad_hyp(E_3)`,
which is `deligne-central-mark-hs-collapse`. By
`deligne-sector-gap-is-exactly-nonhyperlinearity`, `E_3` is then
non-hyperlinear. By `central-extension-kl-schur-criterion` it is also the
only way Kervaire--Laudenbach can fail over `E_3`. The certificate is
finite.

**Also closes the MF-radical goal.** The same certificate excludes both
operator-norm Maslov sectors (`deligne-opnorm-sectors-empty-via-sp4-schur-kernel`),
and with them `deligne-triple-cover-exact-mf-radical`.

**Exact reformulation.** By `central-extension-kl-schur-criterion`, this claim
holds exactly when some nonsingular `w~ in E_3 * <t>` has `z = 1` in
`(E_3 * <t>)/<<w~, [z, t]>>`. Such an identity can be checked exactly: write
elements of `E_3` as pairs `(gamma, k mod 3)` and multiply with Meyer's
cocycle. By `schur-kernel-is-relation-module-homology`, the killed class comes
from the first homology of the relation module of the adjunction.

## Attempts

1. **Finite quotients and known projective representations.** They do not
   help. Every multiplier coming from a projective unitary homomorphism of
   `Sp_4(Z)` vanishes on the Schur kernel
   (`projective-unitary-classes-vanish-on-schur-kernel`). So the killed class
   must lie in the common kernel of all of them. Finite-dimensional
   metaplectic-type representations constrain which multiples of the Maslov
   generator can die. Deligne's theorem shows finite quotients do not see
   the class modulo three, so this route is not blocked. No such common-kernel
   computation has been carried out here.
2. **Aspherical equations.** Dead for this purpose by
   `aspherical-adjunction-has-zero-schur-kernel`. The equation must have a
   non-aspherical relative presentation, with an identity among relations
   whose `Sp_4(Z)`-regions carry Maslov content.
3. **Small or amenable coefficient packets.** Dead by
   `amenable-coefficients-have-zero-schur-kernel`. Localization sends the
   killed class back to the coefficient subgroup `B`, which must be
   non-amenable with non-Connes-embeddable `L_(alpha|B)(B)`, and the class
   must be invisible to every finite quotient of `B`. Packets inside
   unipotent or solvable subgroups, or inside `SL_2(Z) x SL_2(Z)` (Schur
   multiplier seen by its finite abelianization), are excluded.
4. **Direct search.** Not started, and no invariant can prune it. Finite
   quotients, finite-dimensional projective representations, and amenable or
   Connes-embeddable coefficient packets are all blind to the class, by
   `projective-unitary-classes-vanish-on-schur-kernel`,
   `amenable-coefficients-have-zero-schur-kernel` and Deligne's theorem. A
   search is only worth running with a structural candidate in hand: an
   adjunction whose relation module has first homology meeting Meyer's class
   modulo three.
5. **Torsion-free packets.** Dead at amenable shapes by
   `amenable-t-shape-adjunctions-kill-no-schur-class`, however much torsion
   `Sp_4(Z)` has outside the packet. For example, every equation of exponent sum `±1` with
   coefficients in a torsion-free congruence subgroup is excluded. So a
   certificate needs a coefficient subgroup `B` with torsion, or a
   non-amenable reduced `t`-shape: a proper-power shape, or a root with at
   least two clumps. This is a partial pruning invariant for Attempt 4. By
   `kl-holds-over-central-extensions-of-torsion-free-groups`, the preimage of
   a torsion-free `B` in `E_3` satisfies Kervaire--Laudenbach at amenable
   shapes.
6. **Locally indicable packets, at every shape (swarm-0917).** Dead by
   `locally-indicable-packets-have-zero-schur-kernel`. By Howie's restriction
   epimorphism `H^2(B_w; Q/Z) -> H^2(B; Q/Z)`, the Deligne multiplier
   restricted to a locally indicable packet `B` extends over the adjunction,
   so nothing dies. This kills surface, free-by-cyclic, torsion-free
   one-relator and RAAG packets carrying a Maslov class. It also kills every
   class that survives in `H_2` of some locally indicable image of `B`. A
   torsion-free witness packet must therefore be non-locally-indicable, and
   its shape must be non-amenable by Attempt 5.
7. **Finite-cover transfer to a torsion-free square system (swarm-0917).**
   Dead at two steps; see section 5 of
   `research/artifacts/sp4-schur-li-packets-2026-09-17.md`.
   - *At the prime 3.* When `B` has 3-torsion, every permutation extension with
     torsion-free stabilizers has `3 | |X|`, so the transfer loses `alpha`.
   - *At the layered theorem.* The exponent matrix of the square system is not
     unimodular over `Z[P]` in general. For example `2 - zeta_3` has norm 7, so
     Forester--Rourke's layered theorem does not apply.
8. **Refuted (swarm-0917, w4-pull-deligne-1).** The claim is false, by
   `sp4-schur-kernels-miss-every-deligne-multiplier`. The argument has two
   steps.
   - `schur-kernels-are-invisible-to-matricial-windings`: every Schur kernel
     class has eventually zero Exel--Loring winding along every asymptotic
     homomorphism. The route solves `w` exactly in `U(d)` by
     Gerstenhaber--Rothaus and then uses a cancelling relator-commutator
     expansion.
   - Dadarlat's Theorem 3.2 (arXiv:2111.05755), for finitely generated linear
     groups, detects every non-torsion class by a nonzero winding.

   So `K_2(Sp_4(Z), w)` is torsion. The integral Maslov class `e`, and with it
   every `e mod n` including `alpha`, vanishes on it. (MP1.2) can never hold.
