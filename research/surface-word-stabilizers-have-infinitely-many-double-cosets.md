---
rg: 2
id: surface-word-stabilizers-have-infinitely-many-double-cosets
kind: claim
title: The stabilizer in Out(F_2g), g at least two, of the conjugacy class of a one-cusp surface word has infinitely many double cosets, so no subgroup virtually contained in it is a point stabilizer of a type (A) action
requires:
  - out-free-pair-finite-stabilizers-contain-fully-irreducibles
distinct_from:
  out-free-pair-finite-stabilizers-contain-fully-irreducibles: that excludes stabilizers of free factors, free splittings, non-filling classes and points of Outer space as type (A) stabilizers, and names the stabilizer of a filling surface word as the surviving test case; this settles that test case negatively.
  bounded-orbit-subgroups-have-infinitely-many-double-cosets: that uses a bounded orbit in an isometric action; the surface-word stabilizer has unbounded orbits on every standard Out(F_n) complex (it contains geometric fully irreducibles), so this uses a growth count instead.
  out-free-groups-satisfy-boone-higman: that is the open target; this closes one natural shape of a direct type (A) actor, and does not decide the target.
---

**ESTABLISHED** (lane proof, elementary counting plus one cited counting theorem;
not reviewed; no priority claimed).
- **Cited inputs, not read at source this session:**
  - Dehn–Nielsen–Baer for once-punctured surfaces;
  - Mirzakhani, arXiv:1601.03342 (abstract only). She counts closed curves of a
    fixed topological type (one Mod-orbit) by length on S_{g,n}. Only the
    polynomial upper bound is used. Sapir's bounds for curves of bounded
    self-intersection would also suffice.

**Setting.**
- **The surface.** `S = S_{g,1}` is a once-punctured closed orientable surface,
  `g ≥ 2`, with `π_1(S) = F_{2g} = F(a_1,b_1,…,a_g,b_g)`.
- **The class.** `w = [a_1,b_1]⋯[a_g,b_g]` is the peripheral word.
- **The group.** `G = Out(F_{2g})` and `H = Stab_G([w])`, the stabilizer of the
  conjugacy class.
- **Norm.** `‖·‖` is cyclically reduced length in this basis.

**Theorem.** `H\G/H` is infinite. Moreover, if `L ≤ G` and `L ∩ H` has finite
index in `L`, then `L\G/L` is infinite. So no point stabilizer of a type (A)
action of `Out(F_{2g})` is virtually contained in `H`.

**Proof.**
- **Double cosets as orbits.** `H\G/H` is in bijection with the set of `H`-orbits
  on `O = G·[w]`, a set of conjugacy classes.
- **O grows exponentially.**
  - Construction: let `c` be any reduced word in `F(a_2,…,b_g)`, and let
    `θ_c ∈ Aut(F_{2g})` send `a_1 ↦ a_1c` and fix every other generator. Its
    inverse sends `a_1 ↦ a_1c⁻¹`.
  - The word: `θ_c(w) = a_1 c b_1 c⁻¹ a_1⁻¹ b_1⁻¹ [a_2,b_2]⋯[a_g,b_g]`. No letter
    of `c` cancels with `a_1^{±1}` or `b_1^{±1}`, and the last letter `b_g⁻¹`
    does not cancel the first letter `a_1`. So this word is cyclically reduced of
    length `4g + 2|c|`.
  - Injectivity: `a_1` occurs exactly once with exponent `+1`. Rotating to start
    there, `c` is the subword before the first `b_1`. So `c ↦ [θ_c(w)]` is
    injective.
  - Count: the free group `F(a_2,…,b_g)` has rank `r = 2g − 2 ≥ 2`. So
    `#{u ∈ O : ‖u‖ ≤ 4g + 2m} ≥ 2r(2r−1)^{m−1} ≥ 4·3^{m−1}`.
- **H-orbits grow polynomially.**
  - `H` is contained in the stabilizer of the peripheral structure, which is the
    image of the extended mapping class group `Mod^±(S)` (Dehn–Nielsen–Baer). So
    each `H`-orbit `H·u` lies in `Mod^±(S)·u`, which is at most two `Mod(S)`-orbits.
  - The classes `[w]^{±1}` are the only peripheral ones in `O`.
  - Fix a complete finite-area hyperbolic metric on `S`. Every other `u ∈ O` has
    a closed geodesic of length `ℓ(u)`, with `ℓ(u) ≤ K‖u‖`, where `K` is the
    largest length of the generator loops. This is the Lipschitz direction only.
  - A `Mod(S)`-orbit of a closed curve is a fixed topological type. So
    `#{v ∈ Mod(S)·u : ℓ(v) ≤ T} ≤ C_u T^{6g−4}` for large `T`, by Mirzakhani's
    asymptotic with `n = 1` cusp.
  - Hence `#{v ∈ H·u : ‖v‖ ≤ L} ≤ 2C_u (KL)^{6g−4}`.
- **Conclusion.** Finitely many `H`-orbits on `O` would give `O` polynomial
  growth in `‖·‖`, contradicting the exponential lower bound.
- **Subgroups and finite-index overgroups.** If `L ∩ H` has finite index in `L`,
  put `L' = L ∩ H`.
  - `L'\G/L'` maps onto `H\G/H`, so it is infinite.
  - Each `L`-double coset is a finite union of `L'`-double cosets, since
    `[L:L'] < ∞`. So `L\G/L` is infinite.
  - For the type (A) statement, use that a type (A) action has finitely many
    orbits on pairs.

**Calibration.**
- **Genus 1.** For `g = 1`, every automorphism of `F_2` sends `[a,b]` to a
  conjugate of `[a,b]^{±1}` (Nielsen). So `O` is finite and `H` has finite index,
  consistent with `Out(F_2) = GL_2(Z)`. The construction above needs the
  `r = 2g − 2 ≥ 2` letters besides `a_1, b_1`, which is why `g ≥ 2` is assumed.
- **The principle.** The same growth count applies to any class whose stabilizer
  acts through a mapping class group while its `Aut`-orbit grows exponentially.

**Consequence for the direct route to `out-free-groups-satisfy-boone-higman`.**
- **Excluded so far.** With `out-free-pair-finite-stabilizers-contain-fully-irreducibles`,
  a type (A) point stabilizer of `Out(F_{2g})` is not virtually contained in
  either of these:
  - the stabilizer of a free factor, free factor system, free splitting,
    non-filling class or point of Outer space;
  - the stabilizer of a one-cusp surface word.
- **What it must be.** A finitely generated, infinite-index, non-commensurated
  subgroup containing fully irreducibles, not virtually inside either kind of
  stabilizer above.
- **What is not covered.** Stabilizers of other filling conjugacy classes (e.g.
  multi-boundary surface words, or classes whose `Aut`-orbit grows
  subexponentially) are not treated.
