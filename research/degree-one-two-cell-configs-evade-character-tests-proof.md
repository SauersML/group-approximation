---
rg: 2
id: degree-one-two-cell-configs-evade-character-tests-proof
kind: route
title: Read the two w-loops through a spanning tree, compute two abelianized Fox coordinates of the cylinder row whose combination is 1, and certify g in P by a free identity and g not in H by a finite G-set extending the graph
target: degree-one-two-cell-configs-evade-character-tests
requires:
  - two-cell-core-deletions-need-a-unit-fox-coefficient
  - two-cell-ab-nonzero-admissible-needs-g-in-conj-closure
artifacts:
  - experiments/two-cell-character-ideal-2026-09-18/verify1.py
  - experiments/two-cell-character-ideal-2026-09-18/verify2.py
---

The notation is that of the claim. Words use `X = x⁻¹` and `Y = y⁻¹`. Right actions are written
`v^u`, with `v^{uu'} = (v^u)^{u'}`. Every free reduction below is replayed by `verify2.py` for (C2)
and by `verify1.py` for (C1). Neither script imports the census code.

## (C2)

**Step 0: the word.** Take `w = yxYXXyyxYXYxYYxyXy`.
- No two adjacent letters are inverse, and the first letter `y` is not inverse to the last `y`. So
  `w` is cyclically reduced.
- The exponent sums in `x` and in `y` are both 0, so `w ∈ [F, F]`.
- `w` is not a proper power. The only candidate periods are the divisors 1, 2, 3, 6 and 9 of 18,
  and the prefixes `y`, `yx`, `yxY`, `yxYXXy`, `yxYXXyyxY` do not repeat to `w`.

**Step 1: the graph and the two loops.** In `Γ` each vertex has at most one outgoing and at most one
incoming edge of each label, so `Γ` is folded. Reading `w` gives the vertex sequences

- from `3`: `3 3 4 4 3 2 0 1 1 0 0 2 3 3 3 4 4 3 3`;
- from `0`: `0 1 1 0 0 0 1 2 3 3 2 1 1 0 2 3 3 2 0`.

Both paths are closed.

Use the spanning tree `{x: 2→3, x: 3→4, y: 2→0, y: 1→2}`. From `v_0 = 3` its tree paths are
`t_3 = 1`, `t_4 = x`, `t_2 = X`, `t_0 = Xy` and `t_1 = XY`. The five non-tree edges give the basis:

| edge | basis element | word |
|---|---|---|
| `x: 0→0` | `a = t_0 x t_0⁻¹` | `XyxYx` |
| `y: 0→1` | `b = t_0 y t_1⁻¹` | `Xyyyx` |
| `x: 1→1` | `c = t_1 x t_1⁻¹` | `XYxyx` |
| `y: 3→3` | `d` | `y` |
| `y: 4→4` | `e = t_4 y t_4⁻¹` | `xyX` |

Record the non-tree edges crossed along each path. This gives

- `u_0 = d e⁻¹ b c b⁻¹ a⁻¹ d⁻² e d`;
- `u_1 = b c b⁻¹ a⁻² b d⁻¹ c b⁻¹ d`.

Free reduction checks `φ(u_0) = w` and `φ(u_1) = g w g⁻¹`, with `g = t_0 = Xy`. The exponent
vectors in `(a, b, c, d, e)` are `[u_0] = (−1, 0, 1, 0, 0)` and `[u_1] = (−2, 0, 2, 0, 0) = 2[u_0]`.
The vector `[u_0]` is primitive.

**Step 2: two coordinates of `c^ab`.** The abelianization sends `x ↦ t` and `y ↦ s`. So the basis
maps as `a ↦ t`, `b ↦ s³`, `c ↦ t`, `d ↦ s`, `e ↦ s`, and `g ↦ s t⁻¹`.

The Fox derivative counts `+(image of prefix)` at each occurrence of `x` and `−(image of prefix
including x⁻¹)` at each occurrence of `x⁻¹`.

For the coordinate `a`:
- `a` occurs in `u_0` only as `a⁻¹`, after `d e⁻¹ b c b⁻¹`. So `∂_a u_0 ↦ −(s · s⁻¹ · s³ · t · s⁻³ · t⁻¹) = −1`.
- In `u_1`, `a⁻¹` occurs after `b c b⁻¹` and after `b c b⁻¹ a⁻¹`. So `∂_a u_1 ↦ −1 − t⁻¹`.
- Hence `c^ab_a = s t⁻¹ (−1) + 1 + t⁻¹ = (t + 1 − s) / t`.

For the coordinate `c`:
- `c` occurs in `u_0` once, after `d e⁻¹ b`. So `∂_c u_0 ↦ s³`.
- In `u_1`, `c` occurs after `b` and after `b c b⁻¹ a⁻² b d⁻¹`. So
  `∂_c u_1 ↦ s³ + s³ t s⁻³ t⁻² s³ s⁻¹ = s³ + s² t⁻¹`.
- Hence `c^ab_c = s t⁻¹ s³ − s³ − s² t⁻¹ = s² (s² − st − 1) / t`.

Therefore

`(1 + s) c^ab_a + s⁻² c^ab_c = [(1+s)(t+1−s) + s² − st − 1] / t = t / t = 1`.

`verify2.py` computes all five coordinates. It also checks `c^ab · J^ab = 0`, where `J^ab` is the
abelianized `5 × 2` Fox Jacobian of the basis words; this is the `S`-component of the sphere
identity (U1). The remaining three coordinates are not needed.

**Step 3: no character kills `c`.** Let `ρ: G → GL_n(k)` factor through `G^ab`, and set
`σ = ρ(y)` and `θ = ρ(x)`, which commute. Suppose the block row `(ρ(c_x))_x` had rank `< n`.
Applying `ρ` to the identity of Step 2 gives
`(1 + σ) ρ(c_a) + σ⁻² ρ(c_c) = I`, so the block row is onto, a contradiction. This covers every
character, `n = 1`.

**Step 4: `g ∈ P`.** In `F(x,y)` we have

`c⁻¹ · (g d⁻¹ g⁻¹) · d² = XYXyx · XYx · yy = XYXy(xX)Yxyy = XYX(yY)xyy = XY(Xx)yy = XYyy = Xy = g`.

Here `c⁻¹, d² ∈ H` and `g d⁻¹ g⁻¹ ∈ g H g⁻¹`, so `g ∈ P`.

**Step 5: `g ∉ H`, and `C ⊂ X_H`.** Let `x` and `y` act on `{0, …, 8}` by
`x = (2 3 4 5)(6 7 8)` and `y = (0 1 2)(5 6 7)`.
- On `{0, …, 4}` these maps restrict to the edges of `Γ`: `x` fixes 0 and 1 and sends `2→3→4`, and
  `y` sends `0→1→2→0` and fixes 3 and 4.
- The trace of `w` returns every point to itself (nine traces, `verify2.py`). So this is a
  `G`-action, and it is transitive.
- Each element of `H` is the label of a closed path at 3 in `Γ`, so it fixes 3. But `3^g = 3^{Xy} = 2^y = 0`,
  so `g ∉ H`.
- The orbit map `Hu ↦ 3^u` is a graph map from the Schreier graph of `H` onto the orbit graph.
  Composed with `Γ → Sch(H\G)`, it is the inclusion `{0, …, 4} ⊂ {0, …, 8}` on vertices. So `Γ`
  embeds in `Sch(H\G)`, and `e_0` and `e_1` are the `w`-cells at the distinct vertices `H` and
  `Hg`.

## (C1)

This is the same procedure (`verify1.py`).
- **The word.** `w = yXyXyxYxYXXyyxxYXyXyxYxYYYXXyyxYYx` is cyclically reduced, lies in `[F, F]`,
  and is not a proper power.
- **The graph.** `Γ` is folded, and `w` reads closed paths at 0 and at 1.
- **The basis.** Take the spanning tree `{y: 0→1, x: 2→1, x: 3→2}`. It gives `a = x`, `b = y²`,
  `c = yXyxY`, `d = yXXyxxY`, and `g = y`.
- **The loops.** The words are `u_0 = cdCAAbaaBcdCBAAbaBa` and `u_1 = bAcaBddAcaBBddCC`.
  Their exponent vectors are `[u_0] = (0, −1, 0, 2)`, which is primitive, and `[u_1] = 2[u_0]`.
- **The row.** The Fox calculus gives
  - `c^ab_a = s(s−1)(s+1)² t⁻²`;
  - `c^ab_b = s(s−t+1) t⁻²`;
  - `c^ab_d = (s+1)(s²−s−1)`.

  Then
  `s⁻² t c^ab_a − s⁻¹ t c^ab_b − s⁻¹ t⁻¹ c^ab_d = s⁻¹t⁻¹[(s³+s²−s−1) − s(s−t+1) − (s³−2s−1)] = s⁻¹t⁻¹ · st = 1`.
  Step 3 applies verbatim.
- **`g ∈ P`.** We have `Y · yXyxY · y = Xyx` and `x · Xyx · X = y`. So
  `g = a (g⁻¹ c g) a⁻¹ ∈ P`.
- **`g ∉ H`.** Take `x ↦ (1 3 2)` and `y ↦ (0 1)` on `{0, 1, 2, 3}`. This extends `Γ`, kills `w`,
  and sends `0^g = 1`. The embedding argument of Step 5 applies.
- **The kill.** Take `x ↦ (0 1 2)` and `y ↦ (1 2)`, a right action on `{0, 1, 2}` in which `w` acts
  trivially. It gives the ring map `ZG → M_3(F_2)` with `u ↦ M_u`, where `M_u[r, r^u] = 1`, so that
  `M_{uu'} = M_u M_{u'}`.
  - The `3 × 12` block row `(M(c_x))` has rank 2 over `F_2` (`verify1.py`).
  - If `Σ c_x d_x = 1` held, then `Σ M(c_x) M(d_x) = I`, which is impossible at rank 2.
  - So `c` is not unimodular over `ZG`.

## Consequence

A character `χ` kills `c` exactly when `c^χ = 0`. By Step 3 this fails for every character of
(C1) and of (C2). So any two-cell core covered by the step statement is neither `C` of (C1) nor
`C` of (C2).

If `C` of (C2) is a core, it has all of the following:
- degree one with `(a, b) = (1, 2)` (Step 1);
- `g ∈ P` (Step 4) and `g ∉ H` (Step 5);
- no killing character (Step 3).

Every argument that derives `c^χ = 0` from `c^ab`, such as an Alexander-polynomial specialization,
fails on these rows. So a proof of the step must use the injectivity of `π_1(C) → G`. ∎
