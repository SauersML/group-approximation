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
3. **Direct search.** Not started. A search needs a free-group identity
   `r in [F', R_Y][F', <<w~>>]` for a presentation of `Sp_4(Z)`, plus
   evaluation of Meyer's signature cocycle modulo three on `r`.
