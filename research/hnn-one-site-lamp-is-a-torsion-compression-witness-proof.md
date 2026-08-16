---
rg: 2
id: hnn-one-site-lamp-is-a-torsion-compression-witness-proof
kind: route
title: The compressed copy fixes the site, distinct sites commute, properness moves it
target: hnn-one-site-lamp-is-a-torsion-compression-witness
requires: []
artifacts:
  - GroupApproximation/Sofic/AscendingHNNWreathWitness.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise.  Each of the three
conditions in the definition of a torsion compression witness is discharged by
one of the three facts named in the claim.

- `witnessLamp k_0` is the one-site lamp at `t Gamma`; `conj_witnessLamp` shows
  conjugation by an element of the base copy of `Gamma` fixes it, because the
  compressed copy stabilizes the witness site.
- `witnessLamp_pow` transports finite order: if `k_0 ^ m = 1` then the lamp has
  order dividing `m`, since a one-site lamp is a single coordinate.
- `commute_compressed_witnessLamp` and `commute_orbit_witnessLamp` give the
  pairwise commutation of the `L`-orbit, from commutation of one-site lamps at
  distinct sites.
- `isTorsionCompressionWitness_witnessLamp` assembles the three into the
  repository's predicate, for any `m > 0` with `k_0 ^ m = 1`.
- `commutator_witnessLamp_ne_one` is the nontriviality half: for `k_0 != 1` and
  `a_0` outside `alpha(Gamma)`, the site is genuinely moved
  (`smul_tSite_eq_iff`), so the two one-site lamps sit at different sites and
  their commutator is not `1`.

`WreathV`, `baseSub`, `wreathT` and `witnessLamp` are the definitions naming the
four objects; `mem_baseSub_iff` is the membership criterion for the base copy.

## Generality, and one thing to watch

`K` is an arbitrary group and `Gamma` an arbitrary group with an arbitrary
injective endomorphism: no hypothesis beyond `DecidableEq (Cosets alpha hα)`,
which is bookkeeping for the lamp support.  In particular the witness exists even
when `alpha` is surjective — but then `commutator_witnessLamp_ne_one` has no
applicable `a_0`, and the witness is vacuous.  Properness of the self-embedding
is what makes the second half nonempty, and it is required only there.
