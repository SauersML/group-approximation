---
rg: 2
id: module-dual-actions-have-no-wandering-open-sets
kind: claim
title: An infinite group acting by automorphisms on a compact group has no wandering open set, so module triples have no proper open part
distinct_from:
  reduced-group-algebras-contain-no-nonzero-ghosts: that kills ghosts inside the group algebra itself; this kills the proper-orbit architecture of the Higson--Lafforgue--Skandalis coefficients inside every dual-module coefficient algebra.
  amenable-action-invariant-trace-forces-amenability: that shows amenable actions preserve no trace; this uses only the invariance of Haar measure under automorphisms, to force recurrence of open sets.
---

**ESTABLISHED** by `module-dual-actions-have-no-wandering-open-sets-proof`.

Let an infinite countable group `G` act by continuous automorphisms on a compact group `X`,
for example `X = V^` for a countable `Z[G]`-module `V`. Then for every nonempty open
`B ⊆ X`, the set `{g ∈ G : gB ∩ B ≠ ∅}` is infinite. Consequently:
1. no nonempty open `G`-invariant subset of `X` carries a proper `G`-action, and no compact
   open set has pairwise disjoint translates;
2. Haar measure gives a faithful tracial state `tau = m ∘ E` on `C(X) ⋊_r G`. For `X = V^`
   this is the canonical trace of `C*_r(V ⋊ G)`. Every nonzero projection of
   `M_n(C(X) ⋊_r G)` has positive trace.

**Why it matters for `some-nonexact-group-has-a-k-inexact-module-triple`.**
- In the Higson--Lafforgue--Skandalis monster triples (context, not imported):
  - the ideal is the crossed product of the proper open orbit `G`, namely the compact
    operators;
  - the witness ghost lives on that orbit;
  - K-theory detection counts rank along far-away pieces of the orbit.
- In a module triple, `U = X \ Z` is never proper (item 1).
- The faithful Haar trace charges every projection in the kernel of `C(X) ⋊_r G -> C(Z) ⋊_r G`
  (item 2).
- So the Higson--Lafforgue--Skandalis detection has no module version. A module defect must be
  detected by a different invariant.
