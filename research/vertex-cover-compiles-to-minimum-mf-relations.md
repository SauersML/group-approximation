---
rg: 2
id: vertex-cover-compiles-to-minimum-mf-relations
kind: route
title: A length-two return path per undirected edge identifies relation selections exactly with vertex covers
target: minimum-grouped-mf-relations-is-np-complete
requires:
  - minimum-edge-mf-certificate-is-a-directed-cut
  - monotone-mf-implications-use-commuting-involution-relators
artifacts:
  - research/artifacts/pestov91-optimal-mf-certificates-2026-09-13.md
  - research/artifacts/check-pestov91-optimal-mf-certificates-2026-09-13.py
  - research/artifacts/pestov91-optimal-finite-receipt-2026-09-13.json
---

Section 4 groups occurrence edges by their original graph vertex.
Deleting selected groups destroys every return path exactly when the
selected vertices cover every original edge. The cited classical
NP-completeness of vertex cover supplies hardness, while reachability
verifies a guessed selection in polynomial time. The existing formula
compiler keeps the actual expanded group words polynomial in size.
