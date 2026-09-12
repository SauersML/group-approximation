---
rg: 2
id: permanence-closure-evasion-proof
kind: route
title: Push a simple subgroup through each permanence operation until it lands in a sofic, residually finite or free group
target: gottschalk-counterexamples-lie-outside-the-permanence-closure
requires:
  - strict-pairs-transfer-to-table-realizations
  - finitary-split-extension-surjunctivity-permanence
  - graph-folds-over-surjunctive-groups-are-surjunctive
  - lef-lamp-graph-wreaths-are-surjunctive
  - sofic-radical-localizes-garden-of-eden-windows
  - fp-simple-nonsofic-group
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

Derivation: Section 3 of the linked artifact.

**Why every group of `S*` is surjunctive.**
- Sofic groups are surjunctive by the localization claim.
- (O1) and (O2) hold because an automaton runs coset by coset over the subgroup its
  memory generates.
- (O3) is local-embedding closure.
- (O4) to (O7) are the cited permanence theorems.

**Why `Q` never enters.** Induct over the stages of `S*`, supposing `Q` lies in a
group `W` built from groups of an earlier stage.
- **(O1) and (O2).** `Q` already sits in an earlier-stage group. In (O2) this uses
  that `Q` is finitely generated.
- **(O3).** A finite presentation of `Q` has a finite prefix set. An injective
  partial table on that set gives a nontrivial homomorphism into an earlier-stage
  group. Simplicity makes it injective.
- **(O4) and (O7).** `Q` maps trivially to the base, so it lies in the kernel.
  - In (O4), detection gives a site projection that is nontrivial on `Q`, hence
    injective on `Q`, into a residually finite group.
  - In (O7) the kernel is itself residually finite.
- **(O5).** `Q` lies in the kernel of the fold. That kernel meets conjugates of
  vertex groups trivially, so it acts freely on the Bass--Serre tree and is free.
- **(O6).** `Q` lies in a graph product of LEF groups, which is sofic
  (Ciobanu--Holt--Rees 2014, as a directed union over finite subgraphs).

An infinite simple group is not residually finite. It is not free. Being nonsofic,
it lies in no sofic group. The Leavitt consequence uses `fp-simple-nonsofic-group`.
