---
rg: 2
id: nonsofic-lattice-with-dense-projections-in-tree-product
kind: claim
title: Some lattice with dense projections in a product of two type-preserving tree automorphism groups is not sofic
distinct_from:
  radu-bmw-lattice-nonsofic: that is nonsoficity of one explicit lattice with no condition on its projections; this is existence of any nonsofic lattice whose projections are dense in the type-preserving automorphism groups
  f2xf2-admits-nonsofic-action: that asks for any free nonsofic action of F2 x F2; this asks for a nonsofic lattice in the envelope, which gives a mixing one
  nonsofic-hyperbolic-group: that asks for a nonsofic hyperbolic group; lattices in products of trees are never hyperbolic, since they contain Z^2
artifacts:
  - research/artifacts/product-tree-mixing-transfer-2026-09-12.md
---

**OPEN.** For some `p, q >= 3` there is a lattice `Γ <= Aut(T_p)^+ × Aut(T_q)^+` whose
projections are dense in both factors and which is not a sofic group.

By `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action`, such `Γ` gives the
residually finite group `K_p × K_q` (a product of free groups) an essentially free, mixing,
nonsofic p.m.p. action.

**Necessary local condition.** The closure of a projection contains `Aut(T_p)^+` only if the
local action of `Γ` at every vertex of that tree is 2-transitive on the neighbours (the
stabilizer of a vertex in the closure is the closure of the stabilizer in `Γ`, and it must
induce the full symmetric group on the sphere of radius one). This is a finite check.

## Attempts

* **Radu's BMW lattice fails the local condition.** Titz Mite--Witzel's presentation
  `<a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>` gives
  `az = zb`, `by = yc`, `cx = zc`. On the vertical tree `T_v = Γ_R/A` the root stabilizer
  `A = <a,b,c>` acts on the neighbours `xA, yA, zA` by `a ↦ id`, `b ↦ id`, `c ↦ (xA zA)`
  (from `ax = xa`, `ay = ya`, `az = zb`; `bx = xb`, `by = yc`, `bz = za`; `cx = zc`,
  `cy = yb`, `cz = xc`). The local action is `C_2` with the fixed neighbour `yA`, so the
  closure of the vertical projection preserves the perfect matching of `y`-edges and is not
  dense in `Aut(T_3)^+`, nor boundary-2-transitive. On the horizontal tree `T_h = Γ_R/V`, `V`
  acts on `aV, bV, cV` by `x ↦ id`, `y ↦ (bV cV)`, `z ↦ (aV bV)`, which is `S_3`. So even a
  proof of `radu-bmw-lattice-nonsofic` would not feed the transfer theorem with this envelope.
  *No envelope works (ex-tree-lattice-mixing, 2026-09-13).* `radu-lattice-induced-actions-are-never-mixing`:
  the kernel of the horizontal projection is infinite and normal in `H_h × H_v`. So for every
  product envelope, every seed and every cocompact lattice, the induced action is not mixing.
* **Lattices with large local actions.** Burger--Mozes lattices with local actions containing
  `Alt(d)` on both factors pass the local condition; for `d >= 6` Radu (arXiv:1712.01091)
  computes the closures of their projections, which can be proper boundary-2-transitive
  subgroups. The transfer theorem accepts any boundary-2-transitive simple `G_i`, but then a
  sofic lattice of `G_1 × G_2` must be exhibited, since `K_p × K_q` need not lie there. No
  nonsofic lattice of this kind is known.
  *The envelope gap is closed for cocompact lattices (ex-tree-lattice-mixing).*
  `nonsofic-infinitely-transitive-tree-lattice-gives-mixing` puts `G_i = H_i^(∞)`
  (topologically simple by Burger–Mozes Proposition 3.1.2) and uses a free finite-index
  subgroup of the projection of a vertex stabilizer, inside `G_i`, as the sofic lattice.
  The remaining target is `nonsofic-infinitely-transitive-tree-lattice`. By Burger–Mozes
  Theorem 6.5 it contains every one-vertex square complex group.
* **Kun--Thom mechanism.** Unavailable: `Aut(T_p) × Aut(T_q)` has the Haagerup property, and
  so do its lattices, so they contain no infinite Kazhdan subgroup.
