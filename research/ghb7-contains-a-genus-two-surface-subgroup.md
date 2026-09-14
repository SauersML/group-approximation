---
rg: 2
id: ghb7-contains-a-genus-two-surface-subgroup
kind: claim
title: The hyperbolic Kazhdan group GHB_2(7) contains a quasiconvex genus-two surface subgroup
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this answers it for one Kazhdan group outside the classes covered on main
  closed-hyperbolic-3-manifold-groups-contain-surface-subgroups: that is the Kahn--Markovic case; GHB_2(7) has virtual cohomological dimension at most 2, so it is not a closed 3-manifold group
  flip-uniform-lattices-contain-surface-subgroups: that covers uniform lattices under the flip assumption; a uniform lattice with property (T) in a semisimple Lie group has virtual cohomological dimension at least 3, and GHB_2(7) has at most 2
  ghb7-girth-surfaces-give-surface-subgroups: that is the criterion; this is its computer-certified genus-two instance
artifacts:
  - research/artifacts/ideas-growth-hyperbolic-2026-09-14.md
  - experiments/ghb7-girth-surfaces/certificates-genus2.json
  - experiments/ghb7-girth-surfaces/verify_certificate.py
  - experiments/ghb7-girth-surfaces/verify-genus2.log
---

**ESTABLISHED (computer-certified).** `G = G_{HB_2}(7)` contains a quasiconvex subgroup isomorphic
to the fundamental group of the closed orientable surface of genus 2.

Proof: `ghb7-contains-a-genus-two-surface-subgroup-proof`.

## Why this is a new case of Gromov's question on main

`G` is infinite, hyperbolic and has property (T) (item 1 of `cckw-ghb2-kms-group-structure`). By
the standard implication (T) ⇒ FA and Stallings' theorem, `G` does not split and is one-ended. We
did not source-check these two standard facts here.

`G` lies outside every class listed as covered in `one-ended-hyperbolic-groups-contain-surface-subgroups`:
- *Lattices and 3-manifold groups.* The kernel of `ψ` is torsion-free of finite index (item 4) and
  acts freely and cocompactly on the contractible 2-complex `Y`. So `G` has virtual cohomological
  dimension at most 2. That excludes closed 3-manifold groups and uniform lattices with (T).
- *Cyclic graphs of free groups.* `G` does not split.
- *Coxeter groups.* Every finite subgroup of `G` is conjugate into a 7-group (item 4), so `G` has no
  involutions.

We searched the literature only as far as arXiv:1409.1401 and arXiv:1410.4655. Those papers study
periodic apartments and surface subgroups in other groups, torsion-free lattices in triangular
buildings.
