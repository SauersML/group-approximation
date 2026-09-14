---
rg: 2
id: universal-fp-acyclic-group-exists
kind: claim
title: Some finitely presented acyclic group without proper finite-index subgroups contains every recursively presented group
distinct_from:
  labelled-thompson-groups-are-acyclic: that is acyclicity of V(G) for every G; this is the existence of one finitely presented acyclic group containing every recursively presented group, which Palmer--Wu obtain by applying V to a universal finitely presented group.
  labelled-thompson-envelope-properties: that lists properties of the envelope V(G) for each G; this is the single universal group those properties produce.
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

**ESTABLISHED (literature import).** There is a finitely presented group
`U_ac` with `H_n(U_ac; Z) = 0` for all `n >= 1`, with no proper finite-index
subgroups, into which every recursively presented group embeds.

Source: Palmer--Wu, arXiv:2510.16879v1, **Corollary 0.4**, verbatim: "There is
a finitely presented, strongly torsion generated, acyclic group with no proper
finite-index subgroups into which every recursively presented group embeds."
They deduce it from Higman's embedding theorem [Hig61], their Theorem A and
Proposition B.

`U_ac` contains every recursively presented group, so its word problem is
unsolvable.

DERIVATION
universal-fp-acyclic-group-exists-citation
