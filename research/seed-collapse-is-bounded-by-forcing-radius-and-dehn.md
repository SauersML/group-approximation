---
rg: 2
id: seed-collapse-is-bounded-by-forcing-radius-and-dehn
kind: claim
title: For a finitely presented group with a seed, the seed-collapse function κ is at most |Ball(R(n+c))| · δ(2R(n+c)+c), with R the seed's forcing radius and δ the Dehn function, and the word problem runs in time 2^{O(κ̄)} for every computable κ̄ ≥ κ; so the complexity of a seeded group lives in R or in δ, never in how far a nontrivial element must be looked at
distinct_from:
  seeded-groups-have-solvable-word-problem: that shows κ is finite, so the word problem is decidable; this bounds κ above by two intrinsic functions and bounds the word problem above by κ.
  bs12-rigid-seed-is-its-normal-form: that measures one seed, with a linear forcing radius; this is the general sandwich that such measurements feed into.
  heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: that shows seeds from locally finite splittings force at linear radius; this shows that linear forcing leaves all remaining complexity in the Dehn function.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; not reviewed). It sharpens
the CAP remark of `seeded-groups-have-solvable-word-problem`. There, "CAP is a uniform bound
on κ" should read: a uniform computable bound on `κ` over a class implies CAP for that class
(part 2 below), and the converse fails.

## Setting
- `Γ = ⟨Σ | Rel⟩` is finitely presented, with Dehn function `δ` and growth `β(r) = |Ball(r)|`.
- `(Y, p, y_*)` is a seed: SFT rules `𝓡` on word window `U` of radius `u_0`, seed pattern `p`
  of radius `c_p`, `[p] ∩ Y = {y_*}`, `Stab(y_*) = 1`. Rigidity is not used.
- **Certificates.** As in the parent, a *contradiction for `Γ_w`* (`w ≠ 1`) is a finite system
  of constraints on coordinates `x(a)`, `a ∈ F`: rule constraints, the seed constraint, and
  equalities `x(a) = x(b)`, each with a van Kampen diagram for `a^{-1}b` over `Rel ∪ {w}`.
  - Its **size** is the number of coordinates, plus the number of constraints, plus the total
    diagram area.
  - `κ(n)` is the largest, over `w ≠ 1` with `|w| ≤ n`, of the least size of such a
    contradiction.
- **Forcing radius.** `R(r)` is the least `R` such that every pattern on `Ball_Γ(R)` that obeys
  `𝓡` wherever its window fits, and has `p` at `1`, agrees with `y_*` on `Ball(r)`. It is
  finite by compactness, since `[p] ∩ Y = {y_*}`.

## Theorem
1. **Upper bound.** Put `R' = R(n + c_p)`. Then
   `κ(n) ≤ C · β(R') · (1 + δ(2R' + 2u_0 + n))`, with `C` depending only on the finite data.
2. **Lower bound.** For every computable `κ̄ ≥ κ`, the word problem of `Γ` is decidable in
   time `2^{O(κ̄(n))}`, up to the time needed to compute `κ̄`. Equivalently,
   `κ ≳ log T_WP`, where `T_WP` is any lower bound on its time complexity.
3. **The witness costs nothing.** For every `w ≠ 1` there is `v ∈ U_p`, with `|v| ≤ c_p`, such
   that `y_*(wv) ≠ y_*(v)`. So a nontrivial element is always detected inside the seed's own
   window.
4. **`R` is computable.** It is computed from the word problem of `Γ` and the computable
   `y_*`. So `κ` is bounded by a computable function of `(R, δ, β)`.

## Proof
**3.** The pattern `p` occurs in `y_*` only at `1`: if `w^{-1}y_* ∈ [p]`, then
`w^{-1}y_* = y_*`, so `w = 1`. So for `w ≠ 1` some `v ∈ U_p` has
`y_*(wv) = (w^{-1}y_*)(v) ≠ p(v) = y_*(v)`.

**1.** Fix `w ≠ 1` with `|w| ≤ n`, and take `v` from part 3. Put `r = n + c_p`, so `v` and
`wv` lie in `Ball(r)`.
- **Coordinates.** For each `g ∈ Ball_Γ(R')`, choose a geodesic word `rep(g)`.
- **Constraints.**
  - Every rule constraint at `rep(g)` whose window lies in the ball, reading `x(rep(g)u)` for
    `u ∈ U`.
  - The equalities `x(rep(g)u) = x(rep(gu))`, each with a diagram over `Rel` of area
    `≤ δ(2R' + u_0)`.
  - The seed constraint.
  - **One extra equality** `x(rep(v)) = x(rep(wv))`. Here
    `rep(v)^{-1}rep(wv) =_Γ rep(v)^{-1} w rep(v)`, a conjugate of `w`, so its diagram over
    `Rel ∪ {w}` has area `≤ 1 + δ(2r + n)`.
- **Why it is a contradiction.** Diagrams over `Rel` are valid in `Γ_w`, so every constraint
  holds for any configuration over `Γ_w`.
  - Without the extra equality, any solution is a locally admissible pattern on `Ball(R')`
    with `p` at `1` (read through the representatives).
  - By the choice of `R'` it agrees with `y_*` on `Ball(r)`, so `x(rep(v)) = y_*(v)` and
    `x(rep(wv)) = y_*(wv)`.
  - These differ, so the extra equality makes the system unsatisfiable.
- **Size.** The system has `O(β(R'))` coordinates and constraints, and total diagram area
  `O(β(R') · δ(2R' + 2u_0 + n))`.

**2.** Given `w`, enumerate all certificates of size `≤ κ̄(|w|)`. There are `2^{O(κ̄)}` of
them, and each is checked in time `2^{O(κ̄)}`: verify the diagrams, then check
satisfiability by brute force over at most `κ̄` coordinates.
- If one is a contradiction, then `w ≠ 1`.
- If none is, then `w = 1`, because every `w ≠ 1` has a contradiction of size `≤ κ(|w|)`.

**4.** For each `r`, search `R = r, r+1, …`. Compute `Ball(R)` with the word problem, list the
locally admissible patterns with `p` at `1`, and compare them with `y_*` on `Ball(r)`. The
search stops by compactness.

## Answer to "can κ grow arbitrarily fast for rigid seeds?"
- **Where complexity can live.** By part 1, `κ` is fast only through the forcing radius `R`
  or the Dehn function `δ`. The witness never costs anything (part 3).
  - All explicit rigid seeds so far (BS(1,2), H_3(Z), locally finite splittings, tree
    gluing) force at linear radius.
  - For those, `κ(n) ≤ 2^{O(n)} · δ(O(n))`. So their `κ` is fast exactly when `δ` is fast.
- **Distortion (Baumslag–Gersten).** Relative seeds over distorted subgroups make `δ`, and so
  the upper bound on `κ`, non-elementary. But the word problem of the Baumslag–Gersten group
  is polynomial time (Myasnikov–Ushakov–Won; recalled, not re-read). So a fast `κ` bound from
  distortion alone carries **no** ¬CAP content. Part 2 bounds `T_WP` by `κ`, not the other
  way round.
- **Where ¬CAP must come from.** By part 2, it needs rigid-seeded finitely presented groups
  with unboundedly hard word problems, so `κ ≳ log T_WP` is unbounded. Linear forcing does
  not obstruct this: the hardness can sit entirely in `δ`, as in Higman–Clapham towers. So the
  seed-tower target is precisely **a rigid seed with linear forcing radius on a
  machine-simulating tower**. The seed need not compute; the tower's Dehn function does.
- **What CAP would need.** A mechanism by which a rigid seed bounds `δ` or `T_WP`. Parts 1–3
  show the seed's own contribution (`R` and the witness) is independent of `δ`, so no such
  mechanism comes from the forcing structure. CAP stays OPEN. This node only locates it.

## Lesson for general BH
- **The sandwich.** For a finitely presented seeded group,
  `log T_WP ≲ κ ≲ |Ball(R(n))| · δ(O(R(n)))`. The seed's own contribution is only its
  forcing radius. A nontrivial element is always caught inside the seed pattern's window.
- **What it means for CAP.** A seed never has to compute: linear forcing is compatible with
  arbitrarily hard word problems, which then live in the Dehn function. So CAP cannot be
  decided by studying how seeds force.
- **What to build.** The test object is a rigid seed with linear forcing radius on a
  machine-simulating HNN tower. Distortion alone, as in Baumslag–Gersten, inflates `κ`
  without hardness.
