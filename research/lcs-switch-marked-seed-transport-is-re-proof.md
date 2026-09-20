---
rg: 2
id: lcs-switch-marked-seed-transport-is-re-proof
kind: route
title: Enumerate finite marked homomorphism and normal-closure certificates to contradict coHALT
target: lcs-switch-marked-seed-transport-is-re
requires: []
artifacts:
  - research/artifacts/lcs-halting-switch-audit-2026-09-20.md
---

For a finite source K_i, a generator-word substitution into G_e defines
a homomorphism exactly when its finitely many substituted relators have
finite derivations to 1. Enumerate source indices from D, all word
substitutions, and all products of conjugates of target relators proving
these identities. Also enumerate finite products of conjugates of the
resulting marked images and proofs equating such a product to J_e.
All candidate certificates are decidable finite strings. Every membership
J_e in N_D(G_e) has one, so this membership predicate is r.e.

Every homomorphism from G_e to a tracial matrix ultraproduct kills each
transported mark by composition, and therefore kills their normal
closure. The halting-side hypothesis consequently excludes membership
on all halting indices. The nonhalting hypothesis includes every other
index. This would make coHALT r.e.; dovetailing with HALT's recognizer
would decide the halting problem, contradicting diagonalization.

Sections 3-4 of the artifact give the complete proof and the
solution-group specialization. Homomorphism enumeration is standard
(Groves--Wilton, *Enumerating limit groups*, p. 392, footnote 1); the
argument makes no novelty claim for this elementary algorithm and uses
neither a word-problem oracle nor a chosen computable family of maps.
