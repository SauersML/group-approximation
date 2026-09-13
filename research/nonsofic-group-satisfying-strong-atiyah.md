---
rg: 2
id: nonsofic-group-satisfying-strong-atiyah
kind: claim
title: Some nonsofic torsion-free group satisfies the Strong Atiyah conjecture
distinct_from:
  strong-atiyah-torsion-free: that asserts Strong Atiyah for every torsion-free group; this asks for one nonsofic instance, which approximation methods cannot reach and which the conjecture would supply.
  universal-torsion-free-hosts-not-sofic-or-locally-indicable: that shows the universal torsion-free host escapes the sofic, locally indicable and class-C theorems; this asks whether any nonsofic group at all lies in some proved class.
  nonsofic-one-relator-group: that asks for a nonsofic one-relator group; this is the Strong Atiyah consequence such a group would have.
---

**OPEN.** There is a torsion-free group `G` that is not sofic and satisfies the
Strong Atiyah conjecture over `C`: `rk_(N(G))(A) in Z` for every matrix `A` over
`C[G]`.

## Why it is a separate target

**Proved classes.** The classes where Strong Atiyah is proved are:
- locally indicable groups, braid groups, elementary amenable groups, virtually
  compact special groups and 3-manifold groups (Fisher--Ng, arXiv:2606.19606,
  Section 1.1);
- Linnell's class `C`, and residually torsion-free elementary amenable groups;
- subgroups of torsion-free compact `p`-adic analytic groups
  (`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`);
- finite-index subgroups of `Out(A_Gamma)` and of mapping class groups
  (`raag-out-and-mapping-class-virtually-strong-atiyah`);
- graphs of groups with finite edge groups (Sanchez-Peralta, arXiv:2409.12268,
  Theorem 1.1);
- extensions with torsion-free elementary amenable quotient
  (`atiyah-passes-to-torsion-free-elementary-amenable-extensions`) or locally
  indicable quotient (`strong-atiyah-passes-to-locally-indicable-extensions`).

**Only two mechanisms can leave the sofic class.** Take standard facts, recalled
and not re-read here: amenable, residually finite and linear groups are sofic,
and soficity passes to directed unions, to extensions with amenable quotient and
to amalgams over amenable subgroups. Then a nonsofic group in a proved class
needs one of:
1. a locally indicable group that is not sofic;
2. an extension of a Strong Atiyah kernel by a locally indicable, non-amenable
   quotient that is not sofic.

Both are open. Soficity of locally indicable groups is not known, and soficity
is not known to pass to extensions with free quotient (`sofic-semidirect-product-closure-fails`,
section "What is left standing").

**Known torsion-free nonsofic groups are not locally indicable.** These are the
Fournier--Facio group, and the integer-lamp wreaths and doubles over torsion-free
rigid Kazhdan pairs (`left-orderable-non-sofic-via-integer-lamp-rigid-pair`,
`kt-pair-group-double-is-nonsofic`). Each contains an infinite finitely
generated Kazhdan subgroup. By the Attempts of
`left-orderable-group-with-rigid-compression-pair`, no such group is locally
indicable.

## Attempts

* **A nonsofic one-relator group.** Route
  `nonsofic-atiyah-via-nonsofic-one-relator-group`. Any such group is
  torsion-free and locally indicable, so it satisfies Strong Atiyah. Every
  compression mechanism for nonsoficity in this graph uses a Kazhdan subgroup,
  which a locally indicable group cannot contain
  (`torsion-free-one-relator-has-no-kazhdan-subgroup`).
* **An extension with free quotient.** The candidate is the multiple ascending
  HNN extension `E` over an infinite Kazhdan base satisfying Strong Atiyah.
  - By `double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree`, Strong
    Atiyah for `E` needs only `strong-atiyah-kazhdan-edge-amalgam-permanence`,
    iterated along the kernel tree.
  - Whether `E` is nonsofic is undecided: two compressors without ambient (T)
    are left open in `fournier-facio-one-compressor-subgroup-reduces-to-gamma`.
  - The group of `two-variable-kun-thom-actor-satisfies-strong-atiyah` has the
    same compression shape and satisfies Strong Atiyah. But its compressions
    satisfy extra relations and it is residually finite, so it is no witness.
* **Doubles over a rigid pair.** `G *_Gamma G` is nonsofic when `Gamma <= G` is
  an infranormal non-normal Kazhdan pair (`kt-pair-group-double-is-nonsofic`).
  Strong Atiyah for it would follow from Strong Atiyah for `G` together with
  `strong-atiyah-kazhdan-edge-amalgam-permanence`. No torsion-free rigid pair
  with `G` satisfying Strong Atiyah is recorded.
  - The Fournier--Facio pair: Strong Atiyah for that group is open.
  - The characteristic-zero actors with `d >= 3`: Kun--Thom Theorems A and E are
    unchecked in characteristic zero, and there is no locally indicable
    quotient.
  - Kazhdan subgroups of compact `p`-adic analytic groups: the closure of an
    infranormal subgroup is normal (`infranormal-compact-closure-normal`), but
    whether an abstract rigid pair exists inside such a group was not checked.
* **Bounded literature check.** Fisher--Ng Section 1.1, and the 2025-26 arXiv
  searches recorded in `research/artifacts/ex-open-status-2026-09-12.md`, list
  positive classes only. No nonsofic group is named there as satisfying Strong
  Atiyah. None is recorded in this graph.
