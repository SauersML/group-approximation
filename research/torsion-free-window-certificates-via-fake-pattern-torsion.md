---
rg: 2
id: torsion-free-window-certificates-via-fake-pattern-torsion
kind: route
title: A fake in a torsion-free group realizes its own incidence pattern without torsion
target: torsion-free-windows-have-minimal-shannon-certificates
requires: [fake-incidence-patterns-force-torsion]
artifacts:
  - research/artifacts/shannon-fakes-canonical-host-transfer-2026-09-17.md
---
This is artifact Proposition 5(a).

1. Let `G` be torsion-free, and suppose `LP_G(E,F) < 1`.
2. The configuration `(E,F)` realizes its own incidence pattern `P` in `G`, because `G` has exactly the
   coincidences and identity products of `P`.
3. `fake-incidence-patterns-force-torsion` says no torsion-free group realizes `P`, which contradicts step 2.
4. So `LP_G(E,F) >= 1` for every configuration of every torsion-free group.

**Why the prerequisite is worth isolating.** The target can only be refuted by a torsion-free group. The
prerequisite can be refuted, or tested exhaustively, inside finite groups. By the transfer lemma of
`shannon-window-fakes-transfer-to-canonical-hosts`, it reduces to the canonical hosts `H_P`, where every census
fake carries a named two-letter torsion relator.
