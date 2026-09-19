---
rg: 2
id: artin-k4-mixed-dead-character-lies-in-sigma1-proof
kind: route
title: "Novikov homology of A_K vanishes: one unit identity built from the label-6 edge"
target: artin-k4-mixed-dead-character-lies-in-sigma1
requires:
  - novikov-sikorav-h1-criterion-for-artin-sigma1
artifacts:
  - experiments/artin-k4-sigma1-2026-09-17/novikov_unit_identity.py
  - experiments/artin-k4-sigma1-2026-09-17/novikov_unit_identity.log
---

**Notation.**
- `a = u1`, `b = u2`, `c = v1`, `e = v2`, `S_k(z) = 1 + z + ... + z^{k-1}`.
- `N = \widehat{ZG}_χ` is the Novikov ring completed toward `χ -> +∞`.
- `X` is the presentation complex.
- Use the chain complex `N ⊗_{ZG} C_*(X̃)`: row vectors, with the Fox matrix acting on
  the right, so `d_1(y) = Σ y_i (x_i - 1)`.

**Units.** If `χ(g) != 0` then `g - 1` is a unit of `N`. For example
`(a - 1)^{-1} = -Σ_{n>=0} a^n`, and `(c - 1)^{-1} = c^{-1} Σ_{n>=0} c^{-n}`. So all
four `x_i - 1` are units. In particular `H_0 = N / Σ N (x_i - 1) = 0`.

**Fox rows.**
- For `r = (xy)^k (yx)^{-k}`: `∂r/∂x = (1 - y) S_k(xy)` and `∂r/∂y = (x - 1) S_k(yx)`
  in `ZG`. This is checked in the free group ring by the artifact.
- The commutators give the rows `(1 - b, a - 1, 0, 0)` and `(0, 0, 1 - e, c - 1)`.

**Reduction to one ideal.** For `y ∈ ker d_1` put
`φ(y) = y_a (a - 1) + y_b (b - 1) = -(y_c (c - 1) + y_e (e - 1))`.
1. `φ` maps `ker d_1` onto `N`, because `a - 1` is a unit.
2. `ker φ` is the set of `y` whose `u`-part and `v`-part are both torus cycles.
   Since `a - 1` and `c - 1` are units and the torus generators commute, these
   parts are left multiples of the two commutator rows. So
   `ker φ = N·row_u + N·row_v ⊆ im d_2`.
3. A cross row for the edge `u_i v_j` has `φ = (1 - v_j) S_k(u_i v_j)(u_i - 1)`, and
   `1 - v_j` is a unit.

Hence `H_1(X; N) = N / L`, with `L = Σ_{i,j} N · S_k(u_i v_j)(u_i - 1)`, summed over
the four cross edges.

**Unit identity.** In the free group ring `Z F(a, b, c, e)` (artifact, check (2)):

    [S_3(ae) - ae·S_2(ac)](a - 1) + aeab^{-1}[S_2(bc) - S_2(be)](b - 1)
        = (a - 1) + aea(e - c)(a - b).

The left side lies in `L`. It uses the four cross generators `S_3(ae)(a-1)`,
`S_2(ac)(a-1)`, `S_2(bc)(b-1)` and `S_2(be)(b-1)`, with left coefficients in `ZG`.

The right side is `(a - 1)(1 + δ)` with `δ = (a - 1)^{-1} aea(e - c)(a - b)`.
- Each of the four words of `aea(e - c)(a - b)` has `χ = 1` (artifact, check (3)).
- `(a - 1)^{-1} = -Σ_{n>=0} a^n` only raises `χ`.
- So `δ ∈ N` is supported in `χ >= 1`, `1 + δ` is a unit (geometric series), and
  `(a - 1)(1 + δ)` is a unit.

Therefore `L = N` and `H_1(X; N) = 0`.

**Other completion and convention.** The swap `σ : u1 <-> v2, u2 <-> v1` preserves
every label and satisfies `χ ∘ σ = -χ`. It therefore carries this computation to
`\widehat{ZG}_{-χ}`. The involution `g -> g^{-1}` turns the other module convention
into this one with `χ -> -χ`. So `H_0` and `H_1` vanish for both signs and both
conventions.

By `novikov-sikorav-h1-criterion-for-artin-sigma1`, `[±χ] ∈ Σ^1(A_K)` and `ker χ` is
finitely generated.

**Why nothing earlier saw it.** The same identity holds over any ring in which
`a - 1`, `c - 1` and `1 + δ` become invertible. Once `ker χ` is finitely generated,
each `H_1(ker χ; F^d)` is finite-dimensional, hence `F(t)`-torsion. So no
Lemma 3.4 / twisted Alexander / dead-edge-ring / module witness can exist. This
matches the computations in `experiments/artin-k4-sigma1-2026-09-17/`: all
permutation and regular representations through `S_5`, in characteristics 0, 2 and 3,
and the rank-one Groebner bases, are of full rank. The label-6 edge is essential, through `S_3(z) - z S_2(z) = 1`:
- for labels `4,4,4,4` no such unit can exist, since that graph lies in the
  prime-2 family, where the conjecture is proved;
- this is the noncommutative lift of Kochloukova's observation that the four
  dead-edge sums generate the unit ideal of `ZQ`, `Q = G^{ab}`.
