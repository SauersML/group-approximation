---
rg: 2
id: commuting-lamp-quotient-not-mf-lean-direct
kind: route
title: Direct ambient-level formalization of the sign-free collapse
target: commuting-lamp-quotient-not-mf
requires: []
artifacts:
  - GroupApproximation/Sofic/CommutingLampCollapse.lean
---

## Distinct from

- [[commuting-lamp-quotient-not-mf-proof]] — That route first identifies W/<zeta> with F_2[X] semidirect V via the quotient-structure claim and then runs the involutive collapse in the identified model; this one runs the collapse directly in Ambient/<sign> with no structure identification, and is the route that is machine-checked.


## Direct proof, formalized

Work in `H = Ambient(alpha, halpha) / zpowers(signAmbient)` for an
arbitrary injective endomorphism `alpha` of a countable group `Gamma`
with property (T) and a base element `a0` outside the image of `alpha`
— no identification of the quotient with a wreath model is needed.

- The sign subgroup is normal because the sign is central
  (`signZpowers_normal`), and the quotient is countable.
- `L` = image of the base copy under the quotient map; (T) passes to
  `L` through `rangeRestrict` surjectivity.
- The compressor is the image of the stable letter: the ambient
  compression identity descends to the quotient.
- Witness `k` = image of `t c t^{-1}`, which equals the lamp at the
  moved site `tau o` by the ambient conjugation formula.  (W1) lamps
  are involutions; (W2) the compressed base copy fixes the moved site,
  so its image centralizes `k`; (W3) any two conjugates of `k` are
  lamps, whose ambient commutator is the sign — killed in the
  quotient — so the orbit commutes.
- The involutive collapse endpoint
  (`InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness`)
  places `[q(iota a0), k]` in `Rad_MF(H)`.
- Nontriviality: the commutator is `inl` of a product of two lamps at
  the distinct sites `iota(a0) tau o != tau o` (`moved_cosets_ne`);
  the signed finite-support model separates such a product from both
  `1` and the sign, so the commutator is outside `zpowers(sign)`.

Main declarations, in
`GroupApproximation/Sofic/CommutingLampCollapse.lean`:
`commutingLampQuotient_collapse` (generic: radical membership,
nontriviality, and non-MF-ness of the quotient in one statement),
`literalCommutingLampQuotient_collapse` and
`literalCommutingLampQuotient_not_isCDEOperatorMF` (the literal affine
datum, i.e. W/<zeta> itself), with property (T) of the literal base
transported through the affine quotient
(`gammaBar_hasKazhdanPropertyT`).  Authored in the 2026-08-15
generalization wave; the wave's closing validation build certifies the
kernel check.
