---
rg: 2
id: sl3z-is-flexibly-permutation-stable
kind: claim
title: SL_3(Z) is flexibly stable in permutations
distinct_from:
  sl3-z-inverse-3-is-flexibly-p-stable: that is the S-arithmetic group SL_3(Z[1/3]); this is the plain lattice SL_3(Z).
  sln-z-flexibly-hs-stable: that is flexible stability in normalized Hilbert--Schmidt unitary matrices; this is the permutation notion with Hamming distance.
  sl3z-is-stable-in-finite-actions: that asks only for weak containment of limit actions in finite actions; this asks for Hamming correction to genuine actions after vanishing padding.
---

**OPEN.** Every sofic approximation of `SL_3(Z)` is conjugate to a perfect
sofic approximation, in the sense of Bowen--Burton (arXiv:1906.02172). A
finitely presented group has this property whenever it is flexibly P-stable
in the sense of Becker--Lubotzky (arXiv:1809.00632).

## Stakes

- **If true.** `sl3z-thin-free-double-nonsofic-if-sl3z-flexibly-stable` makes
  `SL_3(Z) *_{F_2} SL_3(Z)` nonsofic, where `F_2` is the explicit profinitely
  dense free subgroup. That double is finitely presented.
- **If false.** A single sofic approximation of that double refutes this claim.

## Attempts

1. **The strict form is false.** Bowen--Burton summarize Becker--Lubotzky
   verbatim: "no infinite property (T) group is strictly stable". Only the
   flexible form is at stake.
2. **Bowen--Burton.** They derive a nonsofic group from flexible stability of
   `PSL_d(Z)` for `d >= 5`, and write that they do not know whether `d in {3,4}`
   is possible. The fold theorem
   `codense-tau-amalgams-fold-under-flexible-stability` now covers `d = 3`
   through a plain double.
3. **Status.** No proof and no refutation are known in the sources read: the
   2019 Bowen--Burton text and the graph's `sl3-z-inverse-3-is-flexibly-p-stable`
   Attempts. No later literature was searched.
