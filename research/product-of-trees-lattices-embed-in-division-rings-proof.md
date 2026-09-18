---
rg: 2
id: product-of-trees-lattices-embed-in-division-rings-proof
kind: route
title: Vertex stabilizers of one tree act freely on the other, so the lattice is a graph of free groups with Hughes-free vertex rings
target: product-of-trees-lattices-embed-in-division-rings
requires:
  - compatible-graphs-of-groups-with-loops-embed-in-division-rings
  - fsp-graph-of-rings-and-linnell-extension-imports
---

**1. A graph of free groups.**
- Let `T_1'` be the barycentric subdivision of `T_1`. `Gamma` acts on `T_1'` without inversions.
- Fix a vertex `x` of `T_1'` and put `Gamma_x = Stab_Gamma(x)`. Then `Gamma_x` acts on `T_2`.
- For a vertex `y` of `T_2`, the group `Stab(x) × Stab(y) <= Aut(T_1') × Aut(T_2)` is compact and open, because the
  trees are locally finite. `Gamma` is discrete, so `Gamma_x ∩ Stab(y)` is finite, hence trivial.
- If `g in Gamma_x` inverts an edge of `T_2`, then `g^2` fixes a vertex, so `g^2 = 1` and `g = 1`.
- So `Gamma_x` acts freely without inversions on `T_2`, and it is free (Serre, *Trees*, I.3.3).
- By Bass--Serre theory `Gamma` is the fundamental group of the quotient graph of groups `T_1' / Gamma`. Its vertex
  groups are free and its edge groups are subgroups of them, hence free.
- The quotient graph can be infinite and has loops in general. For a Burger--Mozes one-vertex VH complex, the
  quotient of `T_1` has one vertex.

**2. Compatibility.**
- Let `(G_v, G_e)` be any graph of free groups and `k` any division ring.
- By item 2 of [[fsp-graph-of-rings-and-linnell-extension-imports]] (free groups are residually torsion-free
  nilpotent), each `k[G_v]` has a Hughes-free division ring `D_v`.
- *Condition (3).* By item 1, `Div(k[G_e], D_(t(e)))` is Hughes-free for `k[G_e]`. So is
  `Div(k[G_e], D_(o(e)))`. By Hughes' uniqueness they are `k[G_e]`-isomorphic.
- *Condition (2).* By Gräter (Forum Math. 32 (2020), Corollary 8.3, as quoted in arXiv:2303.08165, Section 2, theorem label `thm:grater`; its printed number was not checked),
  a Hughes-free embedding of a locally indicable group is Linnell. So right transversals of `G_e` in `G_v` are left
  independent over the closure.
- So the graph is D-compatible.

**3. Conclusion.** [[compatible-graphs-of-groups-with-loops-embed-in-division-rings]] embeds `k[Gamma]` in a division
ring `Q`.
- A subring of a division ring has no zero divisors.
- `M_n(Q)` is Artinian, hence directly finite, and direct finiteness passes to `M_n(k[Gamma])`.

**4. Outside the recorded cases.** Take `Gamma` a Burger--Mozes torsion-free finitely presented simple lattice.
- **Residual finiteness.** `Gamma` is infinite and simple, so it is not residually finite. That excludes virtually
  special groups (which are linear over `Z`), 3-manifold groups (residually finite, by Hempel and geometrization),
  and subgroups of `CS(u,d,p)`, which are residually finite.
- **Elementary amenability.** `Gamma` contains `F_2`.
- **Local embeddings.** `Gamma` is finitely presented. A homomorphism to a group `H` that is injective on a ball
  containing a nontrivial element is nontrivial, hence injective by simplicity.
  - So `Gamma` locally embeds into a class closed under subgroups only if it embeds there.
  - That rules out residually finite groups and amenable groups.
- **Strong Atiyah.** In characteristic zero no Strong Atiyah theorem covering `Gamma` is recorded.
  - `Gamma` is not locally indicable, since it is finitely generated, perfect and nontrivial.
  - It is not in Linnell's class `C`. Induction on the class shows that a finitely generated simple group there is
    free or elementary amenable.
- **Unique products.** Whether `Gamma` has unique products is not recorded. The open node
  `some-simple-lattice-in-a-product-of-trees-is-left-orderable` asks for orderability of even one such lattice.

**Calibration.** `F_2 × F_2 <= Aut(T_4) × Aut(T_4)` is the graph of groups with one vertex `F_2` and two loops with
`phi = id`. There `k[F_2 × F_2] = k[F_2][F_2]` is a domain classically, since the group has unique products. The
method reproduces it.
