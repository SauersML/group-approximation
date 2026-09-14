---
rg: 2
id: sp4-schur-kernel-meets-the-deligne-triple-class
kind: claim
title: A nonsingular equation over Sp4(Z) kills a Schur class detected by Deligne's mod-three multiplier
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is an operator-norm emptiness statement about the two nontrivial Maslov sectors; this asks for an algebraic one-variable equation over Sp4(Z) whose adjunction kills a second-homology class on which the mod-three multiplier is nonzero.
  maslov-mod3-projective-defect-gap: that is a uniform analytic defect gap for alpha-projective almost representations; this is a finite algebraic certificate that implies the central collapse without estimating any defect.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
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
