---
rg: 2
id: fp-simple-group-with-kazhdan-subgroup-of-non-residual-centre
kind: claim
title: Some finitely presented simple group has a finitely generated Kazhdan subgroup with infinitely many central elements that die in every finite quotient
distinct_from:
  central-kazhdan-residual-separator-for-boone-higman: that is the separator theorem whose open side this is; this is the existence statement that Boone–Higman forces and that would kill the separator.
  deligne-lattice-satisfies-boone-higman: that asks for Deligne's lattice specifically; this asks for any Kazhdan group with non-residual centre in any finitely presented simple group, which is weaker.
  fp-simple-nonexact-group: that is the existence of a non-exact finitely presented simple group; this is a different predicted monster, witnessed by Kazhdan central extensions rather than expanders.
---

**OPEN.** Boone–Higman implies it: embed Deligne's lattice `Γ~_2`, or `St_3(R_L)`, in a finitely presented simple group (see `central-kazhdan-residual-separator-for-boone-higman`, item 3).

**Statement.** There is a finitely presented simple group `S` and a finitely generated subgroup `K ≤ S` with property (T) such that `Z(K) ∩ R_fin(K)` is infinite. Here `R_fin(K)` is the intersection of the finite-index subgroups of `K`.

**Why it matters.** If it is false, the class `P_Z` separates and Boone–Higman is false, with the finitely presented decidable group `St_N(R_L)` as a witness. If it is true through a construction, the construction is a host of rank at least 2, since every rank-one cone host satisfies the opposite (item 4 there).

**Routes, each on main as an open gate:**
- finite presentation of the finitely generated simple commutator subgroup of the Lagrangian Brin–Thompson group, which contains Deligne's lattice (`deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`);
- a finitely presented simple overgroup of `St_N(R_L)`, which is the GL_n(Q) Steinberg route;
- the rigid-SFT master route (board/SYNTHESIS.md) with `Λ₀ ⊇ Γ~` or `Λ₀ = St_N(R_L)`.

## Lesson for general BH

This is the smallest structural object separating the known hosts from a universal one. Building it is a concrete intermediate milestone toward Boone–Higman. Proving it impossible would refute the conjecture.
