---
rg: 2
id: radu-bmw-lattice-sofic-via-slab-coset-actions
kind: route
title: Embed Radu's lattice in the free generalized wreath product of Z over its arithmetic quotient's action on the oriented edges of the Cayley graph of PGL_2(Z)
target: radu-bmw-lattice-sofic
requires:
  - free-kernel-tree-actions-embed-in-free-generalized-wreath
  - radu-horizontal-slab-coset-actions-are-sofic
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
  the `T_h`-coordinate, and `A = <a,b,c>` is simply transitive on `V(T_h)`, so
  `Stab_(Γ_R)(v_0) = A`. It meets `Λ_v` trivially.
* *Local action on edges.* The relators give `ax = xa`, `bx = xb`, `cx = zc`, `ay = ya`, `by = yc`,
  `cy = yb`, `az = zb`, `bz = za`, `cz = xc`. In `T_v`, `g·(w·v_0) = (gw)·v_0` for `g ∈ A` and
  `w ∈ V`. Hence `a` and `b` fix the `x`-, `y`- and `z`-neighbours of `v_0`. `c` fixes the
  `y`-neighbour and swaps the `x`- and `z`-neighbours: `c·(xv_0) = (zc)v_0 = z v_0`.
* *Orbits and stabilizers.* The oriented edge `v_0 → xv_0` has stabilizer
  `A_c = ker(χ_c)`, and its `Q`-orbit contains its reverse (apply `x`) and the `z`-edges (apply
  `c`). The oriented edge `v_0 → yv_0` has stabilizer `A`, and its orbit contains its reverse (apply
  `y`). So

  ```text
  E^±(Y) ≅ Q/A_c ⊔ Q/A        as Q-sets.
  ```

**Conclusion.**
* *Embedding.* Item 1 of `free-kernel-tree-actions-embed-in-free-generalized-wreath` gives
  `Γ_R ↪ Z ≀^*_(Q/A_c ⊔ Q/A) Q`.
* *Soficity.* Under `radu-horizontal-slab-coset-actions-are-sofic` both orbits are sofic actions of
  the sofic group `Q`, so item 3 of that claim makes `Γ_R` sofic.

**Also obtained.** By item 2 of the same claim, `G_2 = Γ_R/[Λ_v,Λ_v]` embeds in
`Z ≀_(Q/A_c ⊔ Q/A) Q`. So `G_2` is sofic under the same hypothesis, with no quotient by square
boundaries.

∎
