---
rg: 2
id: automatic-groups-satisfy-boone-higman
kind: claim
root: true
title: Every automatic group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over automatic groups, a strictly weaker open problem that the conjecture implies.
  cat0-groups-satisfy-boone-higman: that is item (10) of the survey list, CAT(0) groups; this is item (11), automatic groups, which the survey lists separately.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is item (2) for closed surfaces of genus at least 3; this asks for every automatic group, a class that the survey-status artifact records as containing those mapping class groups.
artifacts:
  - research/artifacts/solve-bh-cat0-automatic-2026-09-13.md
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

**OPEN.** Every automatic group embeds in a finitely presented simple group.

## Where it is asked

- **The question.** Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356, TeX
  fetched on MSI 2026-09-13, Problem `prob:summary`: "Prove the Boone--Higman
  conjecture for: ... (11) Automatic groups."
- **No progress reported.** The survey's Remark `rmk:solved` doesn't mention
  item (11).

## Covered subclasses on main

- **Hyperbolic groups:** `hyperbolic-groups-satisfy-boone-higman`.
- **Braid groups, and mapping class groups of surfaces with a puncture or with
  boundary:** `aut-free-groups-satisfy-permutational-boone-higman`.
- **Spherical-type Artin groups:** `e-type-artin-groups-satisfy-permutational-boone-higman`,
  together with the reduction recorded there.

## Open instances

- **Closed-surface mapping class groups of genus at least 3**
  (`closed-surface-mapping-class-groups-satisfy-boone-higman`). The
  survey-status artifact `research/artifacts/bh-survey-open-cases-status-2026-09-12.md`
  records that the automatic class contains them. That membership was not
  re-read here.
- **No structural method** uses automaticity itself. The rational-embedding
  preprint noted in `research/artifacts/bh-type-a-permanence-2026-09-12.md` §1
  gives no finite presentation of the full groups it builds.

## Attempts

1. **bh-free-21, 2026-09-18: normal-form germ extensions.** Lane proofs, not reviewed.
   - **Source.** BBCMP read at source (preliminary PDF, see
     `research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md` §1):
     - continuous asynchronous automatic groups act on normal-form boundaries by rational
       homeomorphisms (Cor. 1.8–1.9);
     - they say finite presentation of the topological full groups needs "new techniques",
       because the actions are not contracting.
   - **Route.** `automatic-groups-bh-via-normal-form-germ-extensions` replaces contraction by the
     Belk--Hyde--Matucci germ-extension finiteness theorem (`cor:MainFinitenessCorollary`, read
     at source), over the trivial-nucleus boundary Thompson group `B` of the automatic
     structure. It reduces this node to the OPEN premise
     `automatic-groups-embed-in-corner-germ-extensions` (conditions E1–E5).
   - **Calibration.** `z2-free-z-normal-form-boundary-has-corner-singular-orbits` proves E1 and
     E4 for `Z^2 * Z`:
     - four corner singular orbits;
     - germ groups `Z^2` over a `Z` of Thompson germs, quotient `Z`.

     So flats are compatible with this method, unlike finite-nucleus RSG hosts.
   - **Obstruction.** Product normal forms (`F_2 × F_2`, Seifert `F × Z`) give uncountable
     singular sets, so they fail E1. Closed mapping class groups, graph manifold groups and
     large-type Artin groups need non-product structures or supergroups.
   - **More open instances in this class** (automaticity recalled, not re-read):
     - nonfibered closed graph manifold groups (ECHLPT; no Nil or Sol pieces);
     - large-type Artin groups with odd labels (Holt--Rees).
   - **Named questions.** Also asked in BBCMP (p. 7):
     - Q1.15, virtually torsion-free cubulated groups;
     - Q1.16, mapping class groups;
     - Q1.12, finite-type Artin groups, which is answered on main by
       `spherical-artin-groups-satisfy-boone-higman`.
