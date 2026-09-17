---
rg: 2
id: torelli-groups-are-not-cat0-cocompact-stabilizers
kind: claim
title: "No Torelli group in an open case of Zaremsky 3.1 is commensurable with a point stabilizer of a cocompact discrete-orbit CAT(0) action of a finite-index subgroup of its ambient group"
---

**General theorem.** Let `N` be a finitely generated normal subgroup of a group `Γ`,
and suppose `Γ/N` contains a solvable subgroup that is not virtually abelian. Then
there is no action of `Γ` by isometries on a proper CAT(0) space `M` that is
cocompact, has discrete orbits, and has a point `x` whose stabilizer `Γ_x` is
commensurable with `N` (that is, `Γ_x ∩ N` has finite index in both `Γ_x` and `N`).

More precisely, if such an action exists, then there is a finite-index subgroup
`N_1 <= N`, normal in `Γ`, such that `Γ/N_1` acts properly and cocompactly on a
closed convex subspace of `M`; so `Γ/N_1` is a CAT(0) group.

**Torelli corollary.** Let `(G, T)` be one of

- `G` a finite-index subgroup of `Out(F_n)` or `Aut(F_n)`, `n >= 3`, and `T = G ∩ T_n`
  or `T = G ∩ IA_n`;
- `G` a finite-index subgroup of `Mod(S_g)` (closed, or with one marked point or
  boundary component), `g >= 3`, and `T = G ∩ I_g`.

Then no cocompact, discrete-orbit, isometric action of `G` on a proper CAT(0)
space has a point stabilizer commensurable with `T`. The proof is in
`torelli-groups-are-not-cat0-cocompact-stabilizers-proof`.

**What this kills.** Bieri–Geoghegan (*Connectivity properties of group actions
on non-positively curved spaces*, Mem. AMS 161 (2003), no. 765; arXiv:math/9811007,
math/9811008) generalize the Bieri–Neumann–Strebel–Renz invariants from characters
`G -> R^k` to isometric actions `ρ` on proper CAT(0) spaces: for `G` of type `F_m`
and `ρ` with discrete orbits, `ρ` is uniformly controlled `(m-1)`-connected exactly
when `ρ` is cocompact and a point stabilizer has type `F_m`, and this is read off
from `Σ^m(ρ) ⊆ ∂M`. This is the natural non-abelian transplant of the Renz route
already recorded on `ia-automorphism-groups-fp-for-large-rank` (overgroup with
abelian quotient). The theorem shows the transplant has **no admissible input**:
the ambient group, which is of type `F_∞`, cannot be made to act in the required
way with the Torelli group (up to commensurability) as stabilizer. The exact step
where it fails: the quotient `G/T` is a finite-index subgroup of `GL_n(Z)` or
`Sp_{2g}(Z)` and contains a Heisenberg group, which the Solvable Subgroup Theorem
forbids in a CAT(0) group.

**Calibration.** (1) Renz case: `Γ/N ≅ Z^k` acting on `R^k` by translations; the
hypothesis on solvable subgroups fails, and the method is available, as it should
be. (2) `n = 2`: `GL_2(Z)` is virtually free, so `Out(F_2)` acts properly and
cocompactly on a tree through `GL_2(Z)` with finite stabilizers, commensurable with
`T_2 = 1`; the theorem does not apply, consistent with `T_2` being finitely presented.
(3) The theorem asserts nothing about finite presentability, so it cannot contradict
the known cases `T_3`, `IA_3` (not finitely presented).

**Scope.** Not killed: non-cocompact criteria (Brown's criterion on Borel–Serre-type
or outer-space complexes, already recorded as attempts), and actions whose
stabilizers contain the Torelli group with infinite but virtually abelian image in
`GL_n(Z)` (a two-stage Bieri–Geoghegan-then-Renz route). The latter is open.
