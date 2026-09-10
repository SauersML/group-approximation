---
rg: 2
id: fpbs-relative-cycle-dpp-disconnects-proof
kind: route
title: Realize the disconnected FUSF kernel as the relative projection of an explicit source tree
target: fpbs-relative-cycle-dpp-disconnects
requires:
  - fpbs-relative-cycle-operator-descent
  - fpbs-fusf-not-connected-on-some-cayley-graphs
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Section 2 chooses G=T_(2r) x C_M under Pete--Timar Theorem 1.1.
On X x C_M retain a path through every cyclic fiber and all horizontal
tree edges at coordinate zero. Contracting the fiber paths gives
T_(2r), so this is a generating treeing Phi of cost 1+(r-1)/M.
Every ambient edge has positive conditional probability. Since
Z(Phi)=0, its relative operator is P_Z(H), already base measurable.
The complementary determinantal kernel I-P_Z(H) gives FUSF by Lyons,
Determinantal probability measures, Section 3. The imported
disconnection theorem applies. Section 3 proves directly why a
different rule based on finite blocks succeeds in this same example.
