---
rg: 2
id: fg-group-embeds-in-two-generator-simple-acyclic-group
kind: claim
title: Every finitely generated group embeds in a two-generated simple integrally acyclic group
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's small-cancellation envelope for countable groups, whose homology is uncontrolled; this is the Palmer--Wu twisted Brin--Thompson envelope for finitely generated groups, which is in addition integrally acyclic.
  labelled-thompson-groups-are-acyclic: that imports acyclicity of the labelled Thompson groups V(G), which need not be simple (their centre is the centre of G); this imports acyclicity of twisted Brin--Thompson groups, which are always simple.
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

**ESTABLISHED (literature import).** Every finitely generated group embeds,
quasi-isometrically, in a 2-generated simple group `S` with `H_n(S; Z) = 0`
for every `n >= 1`.

Source: M. Palmer and X. Wu, *Embedding groups into acyclic groups*,
arXiv:2510.16879v1, **Corollary 0.10**, verbatim: "Every finitely generated
group embeds quasi-isometrically into a 2-generated, simple, acyclic group."

The envelope is the twisted Brin--Thompson group `SV_G` of the regular action,
`S = G`. Palmer--Wu derive it from:
- their **Theorem C (Theorem 2.22)**, verbatim: "For any group G acting
  faithfully on a countable set S, the associated twisted Brin–Thompson group
  SV_G is acyclic";
- Belk--Zaremsky, [BZ22, Theorems A, B, 3.4].

Their convention, verbatim: "a (discrete) group G is called *acyclic* if it
has the homology of a point."

A countable input reduces to this case after a first embedding into a
finitely generated group, for instance through
`countable-group-embeds-in-two-generator-simple-group`.

**Verification status.** Read from the arXiv PDF on 2026-09-14 (artifact §1).
It is a 2025 preprint. Its inputs were not re-derived: Li's homology theorem
for ample groupoids and [BZ22]. A reading, not a refereeing.
