---
rg: 2
id: radu-delta-squared-orbit-is-signed-permutation-module-proof
kind: route
title: Push the square relators through (xz)^2, read the xz-slab as a simply transitive product of a tree and a line, and identify the orbit of the 4-cycle in the Cayley graph of PGL_2(Z)
target: radu-delta-squared-orbit-is-signed-permutation-module
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-horizontal-projection-kills-delta-squared
  - radu-horizontal-quotient-is-arithmetic-lattice
  - radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups
---

# Proof

**Rewriting rules.** Since all generators are involutions, the relators give

```text
ax = xa,  az = zb,  bx = xb,  bz = za,  cx = zc,  cz = xc,  ay = ya,  by = yc.
```

(`azbz = 1` gives `az = zb` and `zaz = b`, so `bz = za`. `cxcz = 1` gives `cx = zc` and
`x = czc`, so `cz = xc`.)

**Item 1.** Push each horizontal letter through `xzxz` from left to right:

```text
a·xzxz·a = x(az)xz·a = xz(bx)z·a = xzx(bz)·a = xzxz·aa = δ^2,
b·xzxz·b = x(bz)xz·b = xz(ax)z·b = xzx(az)·b = xzxz·bb = δ^2,
c·xzxz·c = (cx)zxz·c = z(cz)xz·c = zx(cx)z·c = zxz(cz)·c = zxzx = δ^(−2).
```

Also `x·xzxz·x = zxzx` and `z·xzxz·z = zxzx`.

**Item 2.**
* *Invariance.* Every `v ∈ V` fixes the base vertex of `T_h`, and every `α ∈ A = <a,b,c>`
  fixes the base vertex of `T_v`. From `ax = xa` and `az = zb`, `a` fixes the `x`- and
  `z`-neighbours of the base vertex of `T_v`. Inductively, `a·w = w·a'` with `a' ∈ {a,b}` for
  every word `w` in `x, z`, so `a` fixes `L` pointwise, and so does `b`. From `cx = zc` and
  `cz = xc`, `c` reflects `L` through the base vertex. So `H_Γ` preserves `T_h × L`.
* *Simple transitivity.* The generators move the base vertex along its edges of `T_h × L`, and at
  every vertex `g·base` with `g ∈ H_Γ` the edges labelled `a,b,c,x,z` are the `g`-translates of
  those at the base, which lie in `T_h × L`. The `{a,b,c,x,z}`-labelled graph of `T_h × L` is
  connected, so `H_Γ` is transitive on its vertices. `Γ_R` is simply transitive on the vertices
  of `T_h × T_v`, so the stabilizer of `T_h × L` equals `H_Γ` and acts simply transitively.
* *Presentation.* `T_h × L` is a simply connected square complex. A group acting simply
  transitively on its vertices, with involutive generators labelling the edges at the base, is
  presented by the involution relators and the boundary words of the squares at the base. This
  is the same principle that gives (RE1). The six squares at the base pair `a, b, c` with `x, z`,
  and their boundary words are cyclic conjugates or inverses of `axax`, `bxbx`, `azbz`, `cxcz`.
* *Kernel.* An element of `H_Γ ∩ Λ_v` fixes the base vertex of `T_h`. It therefore lies in the
  vertex stabilizer, which is `<x,z> ≅ D_∞` acting simply transitively on `L`. By
  `radu-horizontal-projection-kills-delta-squared`, `x` and `z` act on `T_h` as the `a ↔ b` swaps
  in the odd and even `c`-blocks. So `x` and `z` act nontrivially and differently, `xz` acts as the
  global swap, and `(xz)^2` acts trivially. The reflections `xδ^j` act as `x` or `z`, both nontrivial,
  and `δ^j` acts trivially iff `j` is even. So `H_Γ ∩ Λ_v = <δ^2>`.
* *Character.* Each relator of `H_Γ` contains an even number of letters from `{c, x, z}`, so `ψ'`
  is a homomorphism. The conjugation rule holds on generators by item 1, hence on all of `H_Γ`.
  `ψ'(δ^2) = 1`, so `ψ'` descends to `H_Q`.

**Item 3.**
* *Factorization.* `A` is simply transitive on the vertices of `T_h`, and `V` is the stabilizer of
  the base vertex, so `Γ_R = V·A`. Hence `Q = W·A = W·H_Q`. `W ∩ H_Q` is the image of the
  base-vertex stabilizer `<x,z>` of `H_Γ`, which is `D_2`.
* *The fibre.* `V` acts simply transitively on the vertices of `T_v`, and the free group `Λ_v`
  acts freely. So `Y = Λ_v\T_v` is the Cayley graph of `W` on `x, y, z`, and `H_1(Y) = M` with `W`
  acting by deck translations. The loop `wδ^2w^(−1)` has class equal to the oriented 4-cycle
  `w, wx, wxz, wz`, i.e. the coset `wD_2`. In `W ≅ PGL_2(Z)`
  (`radu-horizontal-quotient-is-arithmetic-lattice`), `x` and `z` are distinct commuting
  involutions, so `D_2` has order 4. The components of the `{x,z}`-subgraph of `Y` are exactly these
  4-cycles. They are edge-disjoint, hence linearly independent in `Z_1(Y) = H_1(Y)`.
* *Orbit.* Write `q = w·h` with `w ∈ W` and `h ∈ H_Q`. By item 2, `q·m_0 = ψ'(h)·w·m_0 = ±[wD_2]`.
  So `q·m_0 = ±m_0` iff `w ∈ D_2`, iff `q ∈ H_Q`. The map `Ind_(H_Q)^Q Z_(ψ') → M`,
  `q ⊗ 1 ↦ q·m_0`, is well defined. It sends the basis `Q/H_Q` bijectively, up to sign, onto
  the independent set of 4-cycles `W/D_2`. So it is injective, with image `Z[Q]·m_0`.

**Item 4.** Let `K = ker π`, so that `N = KM/M`. Lift `h` to `ĥ ∈ H_Γ ⊆ Γ_R` and pass to `G_2`.
Since `ĥ ∈ KM`, write `ĥ = kλ` with `k ∈ K` and `λ ∈ M`. By item 2, `ĥδ^2ĥ^(−1) = δ^(−2)` in `G_2`.
`M` is abelian, so `λδ^2λ^(−1) = δ^2`. Therefore

```text
π(δ^(−2)) = π(ĥ δ^2 ĥ^(−1)) = π(k)π(λ δ^2 λ^(−1))π(k)^(−1) = π(δ^2),
```

and `π(δ^4) = 1`. If `ker ψ'` is not closed in the induced topology, then every finite-index
normal `N ◁ Q` has `H_Q ∩ N ⊄ ker ψ'`. Otherwise `ker ψ' ⊇ H_Q ∩ N` would be a union of cosets of
an open subgroup, hence closed. Every finite quotient of `G_2` has such an `N`.

**Reading.** `b` and `c = yby` are conjugate in `Q` and `ψ'(b) = −ψ'(c)`, so no character of `Q`
restricts to `ψ'`. In the translation model on `Q/N × (C_1/B_1)(X_N) ⊗ Z/L`, the class of `δ^2`
at a vertex `p` satisfies `[ℓ_p] = ψ'(h)[ℓ_p]` for every `h ∈ H_Q` fixing `p`. So the mark acts
trivially at `p` whenever the `H_Q`-slice through `p` is `ψ'`-unbalanced.

∎
