---
rg: 2
id: leavitt-units-are-not-conjugate-to-diagonal-copies
kind: claim
title: No unit of infinite order of the binary Leavitt algebra over F_2 is conjugate to its own diagonal copy phi(y) = s_0 y t_0 + s_1 y t_1
distinct_from:
  leavitt-unit-centralizers-have-finite-rank: that bounds centralizer rank, which implies this claim because rank quadruples under phi; this asks only that y and phi(y) lie in different conjugacy classes.
  leavitt-endomorphism-relative-commutants-are-finite: that bounds a whole relative commutant; this excludes a single infinite-order unit of the commutant.
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `Q = R^x`, and `phi(y) = s_0 y t_0 + s_1 y t_1`, which under `R ≅ M_2(R)` is
`diag(y, y)`. For every `y ∈ Q` of infinite order and every `w ∈ Q`, `w phi(y) w^(-1) != y`.

**Why it matters.** `C_R(rho_w(R)) = { z : z = w phi(z) w^(-1) }` (see
`no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`, Attempts). So an infinite-order unit conjugate to
its diagonal copy is exactly an infinite-order unit in some relative commutant. In any unital
`f : L ⊗ L -> L`, `y = f(1 ⊗ c)` is one. So this claim answers Question 5.7 negatively over `F_2`
(`tensor-square-nonembedding-from-no-diagonal-conjugacy`), and it follows from finite centralizer rank
(`no-diagonal-conjugacy-from-finite-centralizer-rank`).

## Attempts

**Rank.** Under `R ≅ M_2(R)`, `C_R(phi(y)) = M_2(C_R(y))`, so `rho(phi(y)) = 4 rho(y)`. `rho` is a conjugacy
invariant with `rho >= 1`.
- *Proved cases.* Every conjugate of a north--south annulus unit, including the non-Thompson twists `c(1 + n)`,
  has `rho = 1` (`leavitt-annulus-north-south-units-have-cyclic-centralizers`). So it is not conjugate to its
  diagonal copy.
- *Where it dies.* No rank bound is known for general linear units.

**Trace (proved necessary condition).** Let `Tr : R -> HH_0(R) = R / [R, R]`.
- `Tr(phi(y)) = Σ_i [s_i y t_i] = Σ_i [t_i s_i y] = 2 Tr(y) = 0`, and `Tr` is conjugation invariant. So
  `y ~ phi(y)` forces `Tr(y^k) = 0` for every `k`. Hence every element of every relative commutant, and every
  element of `f(1 ⊗ L)`, has trace zero.
- **An explicit trace.** For a letter `a`, put `tau_a(s_α t_β) = 1` if `α = βa`, and `0` otherwise.
  - On `R_1^(n) = Hom(V^⊗n, V^⊗(n+1))` this is `Tr((1 ⊗ <a|) x)`, where `<a|` contracts the last output letter.
    Lifting `x -> x ⊗ 1_V` does not change it, so `tau_a` is well defined.
  - *Trace property.* For `x ∈ R_p` and `y ∈ R_(1-p)` at compatible levels,
    `tau_a(yx) = Tr((y ⊗ <a|) x) = Tr(x (y ⊗ <a|)) = tau_a(xy)`, by cyclicity of the matrix trace. So `tau_a`
    kills `[R, R]`.
  - An exhaustive exact check over all 5376 pairs of normal-form monomials of depth `<= 3` with total degree
    `1` found no failure (MSI, `tracecheck.py`).
- **Consequences.** `tau_0(s_0) = 1`, so `HH_0(R) != 0`, consistent with Ara--Cortiñas arXiv:1108.0352v3,
  Corollary 4.5(iii). For the north--south unit, `tau_0(c) = 1` from the term `s_00 t_0`. So `Tr(c) != 0`,
  which is a second proof that `c` is not conjugate to `phi(c)`.
- *Where it dies.* Nothing shows that an infinite-order unit has some `Tr(y^k) != 0`. For example, the classes
  of unipotents `1 + n` with `n` nilpotent in `R_(<0)` often vanish.

**Model test.**
- The trivial unit `y = 1` satisfies `phi(1) = 1`. It is excluded by the infinite-order hypothesis.
- The flip `w = s_00 t_00 + s_10 t_01 + s_01 t_10 + s_11 t_11` gives `rho_w = phi`. Its commutant `M_2(F_2)` contains
  only torsion units, consistent with the claim.

**w22 (swarm-0917-w22-w22-bh-pull, cohomology-index): a complete route.** See
`diagonal-copy-nonconjugacy-from-algebraic-relative-commutants`, which uses
`leavitt-relative-commutants-are-algebraic-over-every-field` (self-contained route
`leavitt-relative-commutants-algebraic-via-fraction-field-koszul`, unreviewed).
- *Mechanism.* Let `y = w phi(y) w^(-1)`. Then `y` commutes with `rho_w(R)`, so `r ⊗ t^j -> rho_w(r) y^j` is a
  unital map `R ⊗ F_2[t] -> R`. It is injective if `y` is transcendental, because `R` is central simple. Then
  `F_2[rho_w(s_0), y]` is a polynomial ring in two variables inside `R`.
- *The invariant.* Suppose `A ⊇ k[a_1..a_n]`, with the `a_i` commuting and independent. Then the fraction-field
  Koszul complex of `a_i ⊗ 1 - 1 ⊗ y_i` gives `w.gl.dim(A ⊗ k(y_1..y_n)) >= n`, with no flatness of `A`. But
  `R ⊗ F_2(y_1, y_2) = L_(F_2(y_1,y_2))(1,2)` is hereditary.
- So `y` is algebraic over `F_2`, hence of finite order.
- *Relation to w18.* This is the same invariant as the w18 node `leavitt-algebras-contain-no-two-variable-polynomial-ring`
  (commit 20e819b457, not yet on main). Here it is re-proved in full so that it does not depend on unlanded files.
- *Effect.* `infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy` is refuted over `F_2`, and its form (b),
  `L ⊗ k[t^±1] ↪ L`, is refuted over every field. The routes `tensor-square-nonembedding-from-no-diagonal-conjugacy`
  and `diagonal-copy-nonconjugacy-from-no-rationals` become redundant. The first now fires. The second is
  unnecessary, and its premise `rationals-do-not-embed-in-binary-leavitt-unit-group` stays OPEN.
- *Maintainer note.* The body line "**OPEN.**" predates this route. Per the contract, this worker edited only this
  section.
