---
rg: 2
id: artin-346-dead-character-outside-sigma1-by-rank-two-rep
kind: claim
title: "A rank-two representation shows that the dead character (1,-1,-1) of the triangle Artin group A(3,4,6) lies outside Sigma^1"
distinct_from:
  artin-346-commutative-rings-miss-the-dead-cut: that shows no commutative coefficient ring detects this character; this detects it with 2x2 matrices
---

Let `A = A(3,4,6) = <a, b, c | abab = baba, acacac = cacaca, bcb = cbc>` and
`χ(a) = 1`, `χ(b) = χ(c) = -1`. The edges `ab` and `ac` are dead, so
`Liv^χ = {a} ⊔ {b–c}` is disconnected, while `Liv_0^χ` is the whole triangle.

Over `F = Q(ω)`, `ω^2 + ω + 1 = 0`, let `y = diag(ω, ω^2)`, `M = [[1, 1], [ω/2, -ω]]`, and

`ρ(a) = M^{-1}`, `ρ(b) = -M`, `ρ(c) = M y`.

Then:

- `ρ(ab) = ρ(ba) = -I`, so the relation holds and `1 + ρ(ab) = 0`;
- `ρ(ac) = y`, `ρ(ca) = M y M^{-1}`, `y^3 = I`, so the relation holds and
  `1 + ρ(ac) + ρ(ac)^2 = 0`;
- `bcb = cbc` reduces to `M y M = -y M^2 y`, and both sides equal
  `[[ω + 1/2, ω - 1], [(ω^2 - ω)/2, ω^2/2 + ω]]`.

So `ρ` is a representation `A -> GL_2(F)` satisfying the hypothesis of
`artin-sigma1-dead-edge-ring-obstruction` for `V_1 = {a}`, `V_2 = {b, c}`, `R = M_2(F)`.
Hence `ker χ` is not finitely generated and `[χ] ∉ Σ^1(A(3,4,6))`.

This agrees with Almeida–Kochloukova's theorem for circuit rank 1. The proof is new
and uses a non-abelian representation. Status: UNREVIEWED.
