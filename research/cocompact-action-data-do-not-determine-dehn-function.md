---
rg: 2
id: cocompact-action-data-do-not-determine-dehn-function
kind: claim
title: "The filling function of a complex, the Dehn functions of the stabilizers and their distortion do not determine the Dehn function of the group"
---

**Statement.** There are two finitely presented groups `G_1`, `G_2`, each
acting cellularly, cocompactly and without inversions on a tree `X_i`, such
that all of the following agree up to `≃`:

- the Dehn function of the complex (`δ_{X_1} = δ_{X_2} = 0`: a tree has no
  2-cells and every edge loop is null-homotopic without any);
- the Dehn functions of all cell stabilizers (every stabilizer is free, and
  every Dehn function involved is `≃ n`);
- the distortion of every cell stabilizer in the group (every stabilizer is
  undistorted),

and yet `δ_{G_1} ≃ n²` while `δ_{G_2} ≃ n`.

So the literal reading of Zaremsky Problem 1.17, that the Dehn function
is *determined by* these three data, is false. The admissible readings are
upper bounds (see `zaremsky-1-17-dehn-function-from-cocompact-action-data`).

**The two actions.** Let `F = F(x, y)` be free of rank 2.

- `G_1 = F × ⟨t⟩`, the HNN extension of `F` in which `t` centralizes `F`.
  Its Bass–Serre tree `X_1` is a line: the vertices are the cosets
  `t^k F` and the edges join `t^k F` to `t^(k+1) F`. Since `F` is normal, it
  fixes every vertex and edge, and `t` acts by translation. There is one orbit
  of vertices and one orbit of edges, and there are no inversions. Every
  vertex and edge stabilizer equals `F`.
- `G_2 = F * ⟨t⟩`, the HNN extension of `F` with trivial associated
  subgroups. Its Bass–Serre tree `X_2` has one orbit of vertices (stabilizers
  the conjugates of `F`) and one orbit of edges (trivial stabilizers), and
  there are no inversions.

**Stabilizer data.** Free groups of finite rank, including the trivial group,
have Dehn function `≃ n` (with the standard convention that Dehn functions of
finitely presented groups are compared up to `≃` and every Dehn function
satisfies `n ≼ δ` after the usual modification). `F` is a retract of both
`G_1` (kill `t`) and `G_2` (kill `t`), so it is undistorted in both, and so are
its conjugates. The trivial subgroup is undistorted.

**Dehn functions.**

- `δ_{G_1} ≃ n²`. Upper bound: `G_1` acts properly and cocompactly on the
  CAT(0) space `T_4 × ℝ` (the Cayley tree of `F` times a line), and CAT(0)
  groups have Dehn function `≼ n²`. Lower bound: `⟨x, t⟩ ≅ ℤ²` is a retract of
  `G_1` (compose `F → ⟨x⟩`, killing `y`, with the identity on `⟨t⟩`); the
  Dehn function of a retract of a finitely presented group is `≼` that of the
  group (Alonso, 1990), and `δ_{ℤ²} ≃ n²`.
- `δ_{G_2} ≃ n`: `G_2 ≅ F(x, y, t)` is free, hence hyperbolic.

**What this does not say.** It does not refute any upper bound of the form
`δ_G ≼ Φ(δ_X, δ_{stabilizers}, Dist_{stabilizers})`: it forces `Φ` to take
the value `≽ n²` on the data `(0, n, n)`, which every known bound does. A
second calibration: `ℤ² = ⟨a, t | [t, a]⟩` and
`BS(1,2) = ⟨a, t | t a t^(-1) = a²⟩` act on their Bass–Serre trees with
infinite cyclic vertex and edge stabilizers; the only datum that differs is
the distortion of `⟨a⟩` in the group (linear in `ℤ²`, exponential in
`BS(1,2)`), and the Dehn functions are `n²` and `2^n`. So any upper bound must
depend on the distortion of the stabilizers in the whole group, not only
inside neighbouring stabilizers (`⟨a²⟩` has index 2 in `⟨a⟩`).
