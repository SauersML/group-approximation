---
rg: 2
id: hnn-one-site-lamp-is-a-torsion-compression-witness
kind: claim
title: A one-site lamp over an ascending-HNN coset space is a torsion compression witness
distinct_from:
  compression-torsion-collapse: that is the analytic collapse theorem, whose hypotheses include a commuting-orbit torsion witness; this supplies such a witness from group theory alone, so that a non-co-Hopfian Kazhdan group is the only structural input the theorem needs.
  multi-mover-collapse-criterion: that is the criterion assembled from the collapse theorem plus the mover analysis; this is one of its structural inputs and asserts nothing analytic.
  ascending-hnn-coset-ray-is-folner: that is the co-amenability datum for the same coset space; this is about a lamp sitting over that space and never mentions means or Folner sets.
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Sofic/AscendingHNNWreathWitness.lean
---

Take any group `Gamma`, an injective `alpha : Gamma -> Gamma`, the ascending HNN
model `V`, its coset space `X = V/Gamma`, and **any** lamp group `K`.  Inside the
permutational wreath product `Wreath K V X` put

- `L` = the base copy of `Gamma`,
- `s` = the stable letter,
- `k` = the one-site lamp carrying a value `k_0` at the witness site `t Gamma`.

Then `k` is a **torsion compression witness** for the marked pair `(L, s)` as
soon as `k_0` has finite order; and every `gamma` outside `alpha(Gamma)` gives a
*nontrivial* collapse commutator `[k, gamma . k]`.

Sections 34.2--34.4 of the dossier, in their algebraic form: this is the
structural input a proper injective self-embedding supplies to the
compression-collapse theorem.

## Why it comes out of three facts already proved

No new mechanism is needed, which is the point:

- the compressed copy of `Gamma` fixes the witness site
  (`iotaVertical_range_smul_tSite`), so conjugating `k` by an element of the
  compressed copy leaves it alone;
- one-site lamps at *distinct* sites commute (`conj_single_commute`), so the
  `L`-orbit of `k` is a commuting family;
- properness moves the site (`smul_tSite_eq_iff`, dossier 34.1: the stabilizer of
  `t Gamma` in `Gamma` is exactly `alpha(Gamma)`), so an element outside the
  image genuinely displaces `k` and the commutator is nontrivial.

Specializing the collapse criterion this way — so that a **non-co-Hopfian Kazhdan
group** is the only structural input — was suggested by Francesco
Fournier-Facio.

## What this does not supply

The analytic gate.  `torsionCollapseDefect_le_actualCoronaMFResidual` still takes
the collapse hypothesis `hkill`, which is discharged unconditionally only for the
involutive subclass (`Sofic/InvolutionCollapseEndpoint`, see
[[involutive-compression-collapse]]).  This claim is the group theory that feeds
that theorem, and it is deliberately independent of `K` — no finiteness, no
abelianness, no residual finiteness of the lamp group is used.
