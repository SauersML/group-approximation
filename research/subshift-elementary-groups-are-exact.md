---
rg: 2
id: subshift-elementary-groups-are-exact
kind: claim
title: EL_3(LC(X,F_2) ⋊ Z) is exact for every infinite minimal subshift X
distinct_from:
  some-simple-kazhdan-lef-groups-are-not-exact: that shows some lamplighter hosts are not exact, through Osajda's groups; this asks whether the Z-subshift groups G_X themselves are exact.
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part1.md
---

**OPEN.** Let X ⊆ A^Z be an infinite minimal subshift and G_X = EL_3(LC(X,F_2) ⋊ Z).

Claim: G_X is exact, that is, it has property A, equivalently C*_r(G_X) is an exact C*-algebra.

- A yes separates the Z-family from the lamplighter hosts on the C*-side: `some-simple-kazhdan-lef-groups-are-not-exact`.
- A no would put a non-exact subgroup inside GL_m(LC(X,F_2) ⋊ Z).

## Attempts
- **Wobbling group / coarse groupoid, dies at isotropy.**
  - G_X acts on F_2^(Z×3), finitely supported vectors in the orbit representation at x, by finite-propagation linear maps. So it moves supports a bounded Hausdorff distance, like a subgroup of a wobbling group.
  - The criterion "βY ⋊ Γ → coarse groupoid of Y is amenable" needs amenable isotropy. Stabilizers of vectors and of ultrafilters are non-amenable.
- **Compact orbit space, dies at fixed points.** G_X acts continuously on K = X × F_2^(Z×3) (all functions), since propagation is finite. An amenable action needs amenable stabilizers, and the zero section is fixed by all of G_X.
- **Tate-space lattices, unresolved.**
  - Through u ↦ shift, G_X acts F_2-linearly on F_2((u))^3 with g(u^n F_2[[u]]^3) ⊆ u^(n−p) F_2[[u]]^3, where p is the propagation.
  - The stabilizer of the standard lattice contains SL_3(LC(X,F_2)), which is locally finite, hence amenable.
  - Property A of the orbit of lattices (a Sato-Grassmannian-type set) is not known, and the codimension-one graph is not locally finite. Dies unless a locally finite G_X-invariant subcomplex with property A is found.
- **Finite asymptotic dimension, dies.** [[T]]′ ≤ G_X contains commuting infinite-order first-return maps to disjoint clopen sets (index-zero combinations). So asdim G_X = ∞ and the Bell–Dranishnikov route to exactness is closed. This is a sketch, not written out.
- **Negative side, unresolved.**
  - A non-exact subgroup must admit banded finite representations of bounded bandwidth (sk-lef-embedding-d, for finitely presented subgroups).
  - The Krylov count of `sk-sl3z-bandwidth` forbids distorted infinite-order elements. It does not forbid growing-girth relator graphs of the Osajda type.
  - No embedding of an Osajda group into GL_m(LC(X,F_2) ⋊ Z) is known.
