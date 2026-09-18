# Referee report (gq-referee-a, proof-gap lens): orbit accumulation forces nontrivial germs

**Reviewed:** `type-a-orbit-accumulation-forces-fg-nontrivial-germs` and its route `-proof` (ae52139fe),
read on origin/main.

**Verdict: PASS.** There is one non-blocking imprecision in the consequences (§3).

## 1. Finite generation and the pair-orbit count

- **Finite generation.** `G_x/N_x` is a quotient of the finitely generated `G_x`.
- **The map is well defined.** It sends `G_x y` to `Γ{x,y}`. It is well defined because `g{x,y} = {x,gy}`
  for `g ∈ G_x`.
- **It is at most two-to-one.** Suppose `γ{x,y} = {x,y'}`.
  - Either `γ ∈ G_x` and `y' ∈ G_x y`,
  - or `γx = y'` and `γy = x`.
  - In the second case, two such `γ_1, γ_2` give `γ_2γ_1^{-1} ∈ G_x` mapping `y'_1` to `y'_2`. So the
    second kind contributes at most one `G_x`-orbit.
- **Consequence.** With hypothesis 2, `G_x` has finitely many orbits on `Γx \ {x}`.

## 2. Nontriviality

- **Setup.** If `G_x = N_x`, then each generator `g_i` is the identity on an open `U_i ∋ x`. So every
  word in the `g_i^{±1}` is the identity on `U = ∩U_i`.
- **Counting.** `X` is Hausdorff, hence T1. An accumulation point of `Γx` therefore has infinitely many
  points of `Γx` in `U`. Each of them is a singleton `G_x`-orbit, which contradicts §1.
- **The quasi-analytic consequence.** `Stab_H(x) ∩ N_x = 1`, so `Stab_H(x)` embeds in `G_x/N_x`.
- **The PGL case.** For `PGL_m(Q)`, the germ group must contain the parabolic `P(Q) ⊇ (Q^{m-1},+)`. By
  O1 it is therefore not residually finite. Correct.
- **Calibration.** The germ group of `V` at `0^ω` is `Z`, via `a − b`. At a point that is not eventually
  periodic, the stabilizer is the identity near `x`, since `uy = vy` with `|u| ≠ |v|` forces
  eventual periodicity. It is a strictly increasing union of the cone stabilizers, so it is not
  finitely generated. Correct.

## 3. Non-blocking

- **"Generic orbits never work"** should read: if every element of `Γ` fixing `x` is the identity near
  `x`, **and `x` accumulates on its orbit**, then the orbit carries no action with hypotheses 1 and 2.
  Without the accumulation hypothesis, a discrete orbit is not excluded.
- In Cantor or `RP^{m-1}` hosts with dense orbits, the hypothesis holds automatically.
