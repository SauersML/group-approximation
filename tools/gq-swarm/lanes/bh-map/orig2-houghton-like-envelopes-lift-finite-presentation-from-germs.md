---
rg: 2
id: houghton-like-envelopes-lift-finite-presentation-from-germs
kind: claim
title: For n >= 3 a Houghton-like group H_n(G) of a finitely generated strongly shift-similar group is finitely presented once its germ group is
distinct_from:
  mz-germ-finite-presentation-lifts-to-the-envelope: that is the lifting gate for E_nu(P) itself, which has only the two "directions" evens/odds and whose E_2-part reproduces the non-finitely-presented Houghton group H_2; this is the lifting gate for H_n(G) with n >= 3 rays, where Houghton's own H_n is finitely presented.
  houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group: that computes the germ group and decides when it is finitely presented; this asks whether finite presentation lifts from the germ group to H_n(G).
  houghton-like-groups-are-strongly-shift-similar: that imports Mallery-Zaremsky Question 5.13 (does G finitely presented imply H_n(G) finitely presented for n >= 3?); this claim implies the positive answer to that part and asks for more, since G itself need not be finitely presented.
---

**OPEN.**

**Statement.** Let `G <= Sym(N)` be a finitely generated infinite strongly shift-similar group, and let `n >= 3`.
If `H_n(G)/FSym([n] x N)` is finitely presented, then `H_n(G)` is finitely presented.

By `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`, the hypothesis says exactly that
`Ĝ = Germs(G) ⋊ <s̄>` is finitely presented. So equivalently: `Ĝ` finitely presented implies `H_n(G)` finitely
presented, for every `n >= 3`.

**Why it matters.**
- For `G = E_nu(P)` with a generic enumeration, the hypothesis holds for every infinite finitely presented `P`.
  So this claim implies `decidable-inputs-have-fp-houghton-like-shift-envelopes`, and through
  `boone-higman-via-houghton-like-shift-envelopes` the Boone--Higman conjecture.
- It also answers the first sentence of Mallery--Zaremsky Question 5.13 positively. If `G` is finitely presented,
  then so is `Germs(G)`, because `FSym(N)` is the normal closure of one transposition. Hence so is `Ĝ`, and this
  claim gives `H_n(G)`.

**Calibrations.**
- **`n >= 3` is needed.** Take `G = FSym(N)`, which is infinite and strongly shift-similar but not finitely
  generated. Then `H_2(G) = H_2`, whose germ group `Z` is finitely presented, while `H_2` is not (K. S. Brown,
  recalled in the source). So `n = 2` fails in general. The f.g. hypothesis excludes this `G` anyway, but the
  Houghton-type obstruction at `n = 2` is the reason for `n >= 3`.
- **Positive cases.**
  - `G = FSym` gives `H_n`, which is finitely presented for `n >= 3` (Brown).
  - `G = H_k` gives `H_n(H_k) = H_(nk)`, finitely presented for `nk >= 3`. This holds even though `H_2` is not
    finitely presented, so finite presentation of `G` is not necessary.
  - `G = E_k`: `H_n(E_k)` contains `H_n(H_k)` with finite index (source, after Question 5.13).
- **First test case.** `P = Z` with a generic enumeration: `R_nu ≅ F_2`, `E_nu(Z)` is not finitely presented, and
  the germ group of `H_3(E_nu(Z))` is finitely presented. Deciding finite presentation of `H_3(E_nu(Z))` is the
  smallest instance, and it would already calibrate the claim beyond the Houghton family.

## Attempts

- **Relator propagation with room.** The attempt recorded on `mz-germ-finite-presentation-lifts-to-the-envelope`
  presents `FSym` by Coxeter relations near one end and propagates them by conjugating with lifts of the germ
  relators. It "works in `H_n` for `n >= 3`, where there is room to commute disjoint moves", and it died for
  `E_nu(P)` because there are only two directions. It ended by asking for an input-dependent "three independent
  directions" condition. `H_n(G)` with `n >= 3` supplies three independent rays by construction, with no condition
  on the input. The remaining obstacle is the one that attempt named: two lifts of the same germ relator differ by
  finitary permutations whose support is not controlled uniformly. This must now be handled inside each ray,
  where `G` acts by an arbitrary strongly shift-similar group rather than by translations. Not carried out.
- **Brown's criterion.** Mallery--Zaremsky sketch a cube complex for `H_n(G)` with vertex stabilizers `G^n`. They
  report that local finiteness fails for infinite `G`, and that the descending links are hard. Not carried out.
