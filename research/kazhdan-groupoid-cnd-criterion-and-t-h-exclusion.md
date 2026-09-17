---
rg: 2
id: kazhdan-groupoid-cnd-criterion-and-t-h-exclusion
kind: claim
title: Property (T) for ergodic measured groupoids is bounded-cnd-on-a-piece, passes to orbit relations, and excludes the Haagerup property
distinct_from:
  haagerup-t-exclusion: that excludes diffuse (T) subalgebras from Haagerup von Neumann algebras; this imports the groupoid-level (T)/(H) exclusion of Anantharaman-Delaroche together with the cnd characterization of relation property (T), which work on pieces of an equivalence relation.
  kazhdan-finite-cocycles-cannot-enter-haagerup-actions: that uses relation (T) against relation (H) in prose for one specific cocycle construction; this is the verbatim import of the general groupoid statements.
artifacts:
  - research/artifacts/kazhdan-relation-coamenability-collapse-2026-09-17.md
---

**ESTABLISHED (import).** C. Anantharaman-Delaroche, "Cohomology of property T groupoids and applications", ETDS
25 (2005), arXiv:math/0308158 (AD05), and "Old and new about treeability and the Haagerup property for measured
groupoids", arXiv:1105.5961 (AD11). The verbatim statements are in Section 1 of the artifact. In summary:

1. **Definition of (T).** A measured groupoid has property (T) if every representation that almost contains unit
   invariant sections contains a unit invariant section (AD05 Def 4.2--4.3). For relations this is Zimmer's
   definition.
2. **cnd criterion (AD05 Thm 5.22).** Let `(G, C)` be an ergodic r-discrete measured groupoid. It has (T) iff for
   every real conditionally negative definite function `psi` there is a positive-measure Borel `E` such that `psi`
   is bounded on `G|_E`.
3. **Orbit relations (AD05 Thm 5.18).** If an ergodic r-discrete groupoid has (T), so does its associated relation.
   For an ergodic p.m.p. action of a countable Kazhdan group, `X ⋊ Gamma` has (T) (AD11, proof of Cor 9.4, citing
   Zimmer Prop 2.4).
4. **Haagerup criterion (AD11 Thm 6.5).** A groupoid has (H) iff it carries a cnd `psi` with
   `nu({psi <= c}) < infty` for all `c`.
5. **Ueda (AD11 Thm 8.4).** Treeable implies (H).
6. **Exclusion (AD11 Thm 9.2).** An ergodic countable measured groupoid on a diffuse standard probability space
   cannot have both (T) and (H).

Nothing is re-proved. The trust surface is the two papers.
