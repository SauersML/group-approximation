---
rg: 2
id: vd-expansion-cube-complex-is-cat0
kind: claim
title: The expansion cube complex of the Higman–Thompson group V_d is a CAT(0) cube complex
distinct_from:
  brin-thompson-nv-stein-farley-complex-is-not-cat0: that shows the analogous complex for nV with n >= 2 is not CAT(0); this is the one-dimensional d-ary case, which should be CAT(0).
---

**OPEN (literature import, not checked at source).** Fix `d >= 2` and let
`C_d = {0,...,d-1}^N`. Let `K_d` be the cube complex with:

- **Vertices:** finite partitions of `C_d` into charted pieces `φ_i(C_d)`, where
  each `φ_i` is a homeomorphism in the prefix-replacement groupoid of `V_d`,
  taken up to permuting the pieces. Equivalently, classes `[φ]` of
  homeomorphisms `φ : ⊔_(i=1)^n C_d -> C_d` that are locally prefix
  replacements, modulo precomposition by permutations of the components. The
  **height** of `[φ]` is `n`.
- **Edges:** split one piece `φ_i(C_d)` into its `d` subpieces `φ_i(jC_d)`.
- **Cubes:** a `k`-cube splits `k` pairwise distinct pieces.

Then `K_d` is a CAT(0) cube complex. `V_d` acts on it by postcomposition, with
finite vertex stabilizers (permutations of the pieces). The height-one vertices
are in bijection with `V_d`.

**Source to check.** Farley constructs proper actions of `F`, `T`, `V` on CAT(0)
cube complexes (IMRN 2003, no. 45, as cited in
`thompson-v-has-haagerup-property-citation`), and treats diagram groups over
semigroup presentations in "Finiteness and CAT(0) properties of diagram
groups" (Topology 42 (2003)). The `d`-ary case should be his complex for the
presentation `⟨x | x = x^d⟩`. Neither PDF has been read in this graph. The
arXiv API was rate-limited on 2026-09-13 and no arXiv copy was located.

**Why it is plausible.** By Chepoi, Roller and Gerasimov, a cube complex is
CAT(0) iff it is simply connected and its 1-skeleton is median. The obstruction
recorded for `nV` comes from pieces split along different coordinate
directions, which cannot happen in the one-dimensional case.
