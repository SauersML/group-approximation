---
rg: 2
id: fp-sofic-kazhdan-group-not-residually-finite
kind: claim
title: Some finitely presented sofic group with property (T) is not residually finite (Alekseev--Thom Open problem 6.1)
distinct_from:
  hyperlinear-fp-infinite-simple-kazhdan-group: that asks for a finitely presented infinite simple Kazhdan group that is hyperlinear, preferably sofic; this drops simplicity and demands soficity, so a sofic simple witness answers both while a hyperlinear one answers neither.
  deligne-triple-cover-is-sofic: that is soficity of one explicit candidate, Deligne's triple cover of Sp_4(Z); this is the existence question it would answer.
  lea-permanence-closure-fp-kazhdan-groups-are-residually-finite: that proves witnesses lie outside the permanence closure of the LEA groups; this is the existence question itself.
artifacts:
  - research/artifacts/sk-fp-sofic-host-status-2026-09-13.md
---

**OPEN.** There is a finitely presented sofic group with Kazhdan's property (T) that is not
residually finite.

It is Open problem 6.1 of Alekseev--Thom, *Centralizers of sofic approximations of Kazhdan groups*,
arXiv:2608.05362. Verbatim from the e-print source, `main_final.tex` l.1732: "Are there examples of
finitely presented sofic groups with Kazhdan's property~\((T)\) that are not residually finite?"

**Why it is hard.**
- A finitely presented LEF, or LEA, Kazhdan group is residually finite.
- More generally, every finitely presented Kazhdan group in the permanence closure of the LEA groups
  is residually finite (`lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`).
- Alekseev--Thom (l.1705--1724) review three regimes:
  - Thom's finitely generated LEF Kazhdan non-residually-finite group, not finitely presented;
  - de Cornulier's finitely presented non-Hopfian Kazhdan groups, with related hyperlinear examples,
    "not known to be sofic";
  - Kar--Nikolov's finitely presented sofic non-residually-finite groups, which "do not have Kazhdan's
    property".

**Routes landed here.** Each is a one-step implication from a recorded open candidate:
- `fp-sofic-kazhdan-non-rf-via-deligne-triple-cover`;
- `fp-sofic-kazhdan-non-rf-via-km-246-lattice`;
- `fp-sofic-kazhdan-non-rf-via-fp-simple-ring`.

## Attempts
- **LEF, LEA, residual amenability.** Dead: with a finite presentation and (T) they force residual
  finiteness (Thom, arXiv:0810.2180, e-print l.263–300).
- **Standard permanence constructions.** Dead by `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`.
  The constructions are subgroups, directed unions, sofic-by-amenable extensions, graphs of groups
  and finite products.
- **Hyperlinear analogue.** Answered by Thom (arXiv:0810.2180, e-print l.263–300). de Cornulier's group
  `K = K_0(Z[1/p])/Z` is finitely presented, non-Hopfian and Kazhdan, and it is hyperlinear, via
  the decomposition of the group von Neumann algebra over the characters of a central subgroup. So
  the unitary form of 6.1 has an answer, and only the permutation form is open. The central-character
  decomposition has no recorded permutation analogue.
- **Finite-central-by-residually-finite permanence.** Open, and it would suffice: Deligne's triple
  cover is such an extension. Glebsky (Rev. Mat. Iberoam. 39 (2023) 1097--1104) proves the weakly
  sofic version. For soficity he records only the hope, going the other way, that such extensions
  give non-sofic groups.
