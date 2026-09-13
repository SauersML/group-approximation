---
rg: 2
id: radu-bmw-lattice-sofic-via-slab-coset-actions
kind: route
title: Embed Radu's lattice in the free generalized wreath product of Z over its arithmetic quotient's action on the oriented edges of the Cayley graph of PGL_2(Z)
target: radu-bmw-lattice-sofic
requires:
  - free-kernel-tree-actions-embed-in-free-generalized-wreath
  - radu-edge-coset-action-is-sofic
  - sofic-set-actions-pass-to-finite-fibred-quotients
  - radu-horizontal-tree-group-is-linear
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

# Derivation

**Setup.**
* *Tree and kernel.* Take `Γ = Γ_R`, `T = T_v` and `Λ = Λ_v = ker(Γ_R → Aut(T_h))`. `V = <x,y,z>` acts
  simply transitively on the vertices of `T_v` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).
  `Λ_v ⊆ V` is free (`radu-horizontal-tree-group-is-linear`), so it acts freely on vertices. It
  inverts no edge, since an inversion has square fixing a vertex, hence is torsion.
* *Quotient.* `Q = Γ_R/Λ_v` is finitely generated linear, hence residually finite and sofic.
  `Y = Λ_v\T_v = Cay(W; x,y,z)` with `W ≅ PGL_2(Z)`.

**The Q-set of oriented edges.**
* *Vertex stabilizer.* `Γ_R` is simply transitive on `V(T_h) × V(T_v)`. Horizontal letters move only
  the `T_h`-coordinate, and `C = <a,b,c>` is simply transitive on `V(T_h)`, so `Stab_(Γ_R)(v_0) = C`.
  It meets `Λ_v` trivially.
* *Local action on edges.* The relators give `ax = xa`, `bx = xb`, `cx = zc`, `ay = ya`, `by = yc`,
  `cy = yb`, `az = zb`, `bz = za`, `cz = xc`. Since `g·(w·v_0) = (gw)·v_0` in `T_v`, `a` and `b` fix
  the `x`-, `y`- and `z`-neighbours of `v_0`, while `c` fixes the `y`-neighbour and swaps the other
  two: `c·(xv_0) = (zc)v_0 = zv_0`.
* *Orbits and stabilizers.* The oriented edge `v_0 → xv_0` has stabilizer `C_χ = ker(χ : c ↦ −1)`.
  Its `Q`-orbit contains its reverse (apply `x`) and the `z`-edges (apply `c`). The oriented edge
  `v_0 → yv_0` has stabilizer `C`, and its orbit contains its reverse (apply `y`). So
  `E^±(Y) ≅ Q/C_χ ⊔ Q/C` as `Q`-sets. This agrees with item 1 of
  `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`.

**Conclusion.**
* *Both orbits are sofic.* Assume `radu-edge-coset-action-is-sofic`, i.e. `Q ↷ Q/C_χ` is sofic. Then
  `Q ↷ Q/C` is sofic by `sofic-set-actions-pass-to-finite-fibred-quotients`, applied to
  `Q/C_χ → Q/C` with fibres of size 2.
* *Embedding.* By item 1 of `free-kernel-tree-actions-embed-in-free-generalized-wreath`,
  `Γ_R ↪ Z ≀^*_(Q/C_χ ⊔ Q/C) Q`.
* *Soficity.* Item 3 of that claim makes the free generalized wreath product sofic, and hence `Γ_R`.

**What this adds to the metabelian route.** `radu-metabelian-quotient-sofic-via-edge-coset-action`
derives soficity of `G_2 = Γ_R/[Λ_v,Λ_v]` from the same action, through restricted lamps. With free
lamps the same single set action gives soficity of Radu's lattice itself. No marked limit over the
lower central series of `Λ_v` is needed.

∎
