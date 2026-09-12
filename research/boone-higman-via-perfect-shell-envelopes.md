---
rg: 2
id: boone-higman-via-perfect-shell-envelopes
kind: route
title: Embed the input in a perfect decidable finite presentation and present its already simple shell group
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-fp-groups-embed-in-perfect-decidable-fp-groups
  - perfect-input-shell-envelopes-are-simple
  - perfect-decidable-inputs-have-fp-shell-envelopes
artifacts:
  - research/artifacts/boone-higman-perfect-shell-route-2026-09-08.md
---

Given a finitely generated group G with decidable word problem,
Clapham embeds G in a finitely presented group P_0 with decidable
word problem. The explicit perfect-envelope construction embeds
P_0 in an infinite perfect finitely presented group P=W(P_0)
whose word problem remains decidable.

Apply the OPEN hypothesis for perfect inputs to choose nu with
E_nu finitely presented. The shell simplicity claim makes E_nu
simple for this same nu, and the construction embeds P in E_nu.
The composite G->P_0->P->E_nu is therefore an embedding into a
finitely presented simple group.

The final group is the shell envelope itself. No additional twisted
Brin--Thompson group, finite presentation of singularity stabilizers,
or finite presentation of the germ quotient is assumed in this route.
The only unresolved construction is the named presentation hypothesis
for perfect inputs. Neither an embedding in a perfect group nor
simplicity of its shell envelope proves that hypothesis.
