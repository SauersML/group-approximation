---
rg: 2
id: simple-algebra-completions-have-no-scalar-points-proof
kind: route
title: Trace-kernel ideals vanish in simple algebras, and Glimm halving gives a nowhere-small order zero M_2
target: simple-algebra-completions-have-no-scalar-points
requires: []
---

Notation as on the target.

**Part 1.** For a tracial state `τ`, put `N_τ = {x ∈ A : τ(x*x) = 0}`.
- It is a left ideal: `(ax)*(ax) = x*a*ax ≤ ‖a‖² x*x`.
- It is a right ideal: with `y = xa`, traciality gives `τ(y*y) = τ(yy*) = τ(x aa* x*) ≤ ‖a‖² τ(xx*)`,
  and `τ(xx*) = τ(x*x) = 0`.
- It is closed, by continuity of `τ`, and proper, since `τ(1) = 1`.
- `A` is simple, so `N_τ = 0`.

For self-adjoint `h` with `μ = τ(h)`, `Var_τ(h) = τ((h − μ)²) = ‖π_τ(h) − μ1‖²_{2,τ}`.
- If `π_τ(h) = c1` in `π_τ(A)″`, applying the normal extension of `τ` gives `c = μ`, so
  `Var_τ(h) = 0`. Then `h − μ ∈ N_τ = 0`, so `h` is scalar.
- `τ ↦ Var_τ(h)` is weak*-continuous and positive on the compact set `K`, so its minimum is
  positive.

**Part 2.** `τ(a) = τ((a^{1/2})* a^{1/2}) > 0`, because `a^{1/2} ≠ 0` and `N_τ = 0`. The minimum
over the compact `K` is attained, hence positive. If `π_τ(a) = 0` then `τ(a) = 0`.

**Part 3.** `A` is simple and non-elementary, so Glimm's halving lemma gives a nonzero
`*`-homomorphism `ρ: C_0((0,1]) ⊗ M_2 → A`. This is standard, e.g. Kirchberg–Rørdam,
*Non-simple purely infinite C*-algebras*, Proposition 4.10; not re-read by this lane.
`φ(x) = ρ(id ⊗ x)` is c.p.c. order zero with `φ(1) ≠ 0`, so Part 2 gives `min_K τ(φ(1)) > 0`.

**Part 4.**
- **`ε_0 < 1`.** An eigenprojection of trace `1` means `π_τ(h)` is scalar, which Part 1 excludes
  for non-scalar `h`. Non-scalar self-adjoint elements exist because `A ≠ C`.
- **The bound.** Take c.p.c. order zero `φ: M_2 → A`, `c = φ(1)`, and the supporting
  homomorphism `π` into `π_τ(A)″` with `c` commuting with `π(M_2)` and `φ = c·π`
  (Winter–Zacharias; standard). Put `h = φ(e_11) − φ(e_22) = c·π(e_11 − e_22)`.
  - The eigenvalue `0` has eigenprojection `1 − supp(c)`, and `1 − supp(c) ≤ 1 − c`, so its trace
    is `≤ 1 − τ(c)`.
  - A nonzero eigenvalue `±s` has eigenprojection `π(e_ii)·1_{{s}}(c)`, which is equivalent to
    `π(e_jj)·1_{{s}}(c)` for `j ≠ i` through `π(e_ij)`. So its trace is `≤ 1/2`.
  - Suppose `ε_0 > 1/2`. Rigidity gives `τ ∈ K` with an atom of mass `≥ ε_0` for `h`. That atom is
    at `0`, so `1 − τ(c) ≥ ε_0`. Hence `min_K τ(φ(1)) ≤ 1 − ε_0` for every `φ`.

**Rigidity ⟹ indivisibility.** For order zero `φ: M_N → A` with `τ(1 − φ(1)) < ε` on `K`, take
`h = Σ_j (j/N) φ(e_jj) = c·π(Σ_j (j/N) e_jj)`.
- Eigenvalue `0`: trace `≤ τ(1 − c) < ε`.
- Eigenvalue `s ≠ 0`: the eigenprojection is `Σ_j π(e_jj)·1_{{sN/j}}(c)`. Through `π(e_1j)`, which
  commutes with `c`, each piece has the trace of `π(e_11)·1_{{sN/j}}(c)`. The values `sN/j` are
  distinct, so these spectral projections of `c` are orthogonal, and the total trace is
  `≤ τ(π(e_11)) ≤ 1/N`.
- So `ε_0 > max(1/N, ε)` contradicts rigidity. No comparison hypothesis is used.
