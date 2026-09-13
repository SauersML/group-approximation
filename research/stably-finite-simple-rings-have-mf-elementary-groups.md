---
rg: 2
id: stably-finite-simple-rings-have-mf-elementary-groups
kind: claim
title: Is stable finiteness of a simple ring enough for its elementary groups to be MF in every rank?
distinct_from:
  mf-elementary-groups-force-stably-finite-simple-rings: that proves stable finiteness is NECESSARY for stably MF elementary groups; this asks whether it is SUFFICIENT
  stably-mf-elementary-groups-force-matricial-rings: that asks for the opposite strengthening, that stably MF elementary groups force exact matricial embeddability; the two open claims bracket the true ring-level condition
---

**OPEN.** Let `R` be a countable simple unital ring that is stably finite. Is `EL_N(R)` MF for every `N >= 3`?
The weaker form asks whether `EL_N(R)` has a nontrivial MF quotient for every `N`.

Either answer sharpens the UN boundary (`research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md`
§0):
- **If true.** For simple rings, stable MF of the Kazhdan groups `EL_N(R)` is exactly stable finiteness. That is
  a ring-level characterization of operator-norm approximability for this class. With
  `mf-elementary-groups-force-stably-finite-simple-rings` it would be an equivalence.
- **If false.** Some simple stably finite ring kills MF approximations of its elementary groups by a mechanism
  other than one-sided compression. That would be a new non-MF mechanism.

## Attempts

- **Through exact matricial models (partial).** `exactly-matricial-rings-have-lef-general-linear-groups` proves
  the conclusion, with LEF, for exactly matricial rings. It does not reach every stably finite simple ring.
  Greenfeld arXiv:2210.11650 gives finitely generated stably finite algebras that are not even linear sofic,
  though not simple. So stable finiteness alone does not supply ring models, and a proof must build MF models
  of `EL_N(R)` that are not induced by ring homomorphisms. (Source relayed by `un-prior-art`; verbatim check
  owed.)
- **Through the C*-algebraic MF problem (no mechanism).** MIP* = RE yields a stably finite non-MF C*-algebra
  (`non_mf_groups_exist.tex` l.315–320). Transferring that to a simple ring `R` and to the non-unitary groups
  `EL_N(R)` needs a way to turn operator-norm models of `EL_N(R)` into models of `R`, and none is known.
- **Through the compression criterion (dies).** Every compressor built so far comes from a one-sided inverse in
  some `M_m(R)`. Compressors alone do not kill MF: `k[BS(1,2)]` is exactly matricial, yet `u k[y] u^-1 = k[y^2]`
  gives `u EL_3(k[y]) u^-1 < EL_3(k[y])`. What matters is a *full defect idempotent*, and in a stably finite
  simple ring every one-sided inverse is two-sided at every matrix size.
