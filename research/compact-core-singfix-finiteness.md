---
rg: 2
id: compact-core-singfix-finiteness
kind: claim
title: Faithful compact annular cores give all marked SingFix groups and clopen actors type F_k
distinct_from:
  dynamically-v-separated-groups-satisfy-boone-higman: that uses one-sided one- and two-point groups for finite presentation; this uniform claim requires all relevant marked sets, depth-zero base isotropy, and finite-forest restriction groups.
  zoom-tower-germ-groups-give-f-infinity-germ-extensions: that uses towers over cyclic prefix germs; this allows a general faithful depth-preserving profile group containing the entire depth-zero base isotropy.
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

**OPEN — substantive uniform finiteness lemma; submitted proof pending independent review.**

For `k≥2` or `k=∞`, assume the compact-core data of artifact §3:
type `F_k` finite-forest bases; finitely many oligomorphic marked
species; faithful type `F_k` profile groups `L` containing the entire
depth-zero base isotropy `H` of type `F_k`; locally base annular actions
and base finite-band cutoffs; injective advance maps realized by inverse
zoom up to finite-band base corrections; actual ascending HNN isotropy
germs with nonzero zoom depth; and well-defined full finite germ
extensions with single-germ localization and the stated base charts.
Assume the same structural data in every relevant finite forest.
Require enough base prefix maps to realize the stated marked-tuple
and Boolean-atom matches, and require that the full restriction group
on each nonempty clopen atom is exactly the corresponding finite-forest
construction, with compatible charts and allowed germs. These are
structural hypotheses, not consequences of an arbitrary base action
on a regular-tree boundary. The forbidden-singularity `H`-only data,
including type `F_k`, are separate hypotheses and do not follow from
`H≤L` and type `F_k` for `L`.

Then for every finite `M⊆P`, the group `SingFix_Γ(M,P)` is an actual
iterated ascending HNN extension of
`B_C×∏_{p∈M}L_p×∏_{p∈P\M}H_p`, hence has type `F_k`.
Every finite-forest host `Γ` has type `F_k`. Its action on proper
nonempty clopens is faithful and oligomorphic, and all finite-subset
stabilizers of this action have type `F_k`.

## Attempts

The proposed proof is detailed in artifact §3. Choose disjoint buffers,
an actual disjoint-support core, and commuting contractions. Inverse
conjugation preserves the core by a shifted inner profile plus a base
outer-band correction. Match finitely many germs, then express the
remaining base element trivial near the marked points as a conjugate
of the complement base. At each successive HNN stage, the new depth
character detects the difference of stable-letter exponents; the
previous stage has depth zero there. This is intended to prove
injectivity of the actual HNN model rather than merely a surjection.

The local support, surjectivity, all-stage injectivity, and full
finite-forest restriction statements remain to be verified. There is
only one local factor at each point: inserting `L×H` when `H≤L` is
incorrect. Clopen orbit classification requires cone-count residues
as well as Boolean atoms in nonbinary degree. Belk–Hyde–Matucci
2407.03149v1 **Theorem 2.1**, finite-forest base finiteness, and the
standard HNN/product/finite-extension closure facts are explicit
classical inputs. No assertion that the original base germ is normal
is needed; no theorem or Lean proof currently discharges this gate.
