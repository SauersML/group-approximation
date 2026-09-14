---
rg: 2
id: thompson-f-metabelian-commutator-bound-proof
kind: route
title: The commutator is three relator conjugates modulo the second derived subgroup, by Fox calculus on the grid, and metabelian images kill the rest
target: thompson-f-metabelian-pairs-obey-sharp-linear-commutator-bound
requires: []
---

Numbering follows the claim. `Z[Z^2] = Z[s^±1, t^±1]`, with `a ↦ s` and `b ↦ t`.

**0. Fox derivatives are edge counts on the grid.** Let `Γ` be the Cayley graph of `Z^2` with edges
`p → p + (1,0)` labelled `a` and `p → p + (0,1)` labelled `b`.
- A word `w` has exponent sums zero exactly when its walk from `0` in `Γ` is closed. So
  `F_2' = π_1(Γ, 0)`, and since `Γ` is a graph, `H_1(Γ) = F_2'/F_2''` (abelianization of `π_1`), and
  `H_1(Γ)` is the cycle space, a subgroup of the chain group `C_1(Γ) = Z[Z^2] e_a ⊕ Z[Z^2] e_b`.
- The 1-chain of the walk of `w = y_1 ⋯ y_m` is `(∂w/∂a) e_a + (∂w/∂b) e_b`, where the Fox derivative
  `∂w/∂a = Σ_(y_k = a) ȳ_1⋯ȳ_(k-1) − Σ_(y_k = a^-1) ȳ_1⋯ȳ_k` records each `a`-edge by its lower endpoint
  with the sign of traversal, and likewise for `b`.
- **Criterion.** For `w ∈ F_2'`: `w ∈ F_2''` exactly when `∂w/∂a = ∂w/∂b = 0` in `Z[Z^2]`.
- **Winding functions.** For `w ∈ F_2'`, `(∂w/∂a)(s - 1) + (∂w/∂b)(t - 1) = 0`, so `∂w/∂a = W(w)(t - 1)`
  for a unique `W(w) ∈ Z[Z^2]`. Then `W(ww') = W(w) + W(w')`, `W(g w g^-1) = ḡ W(w)` and
  `W(w^-1) = -W(w)`.

**1. The identity (item 2).**
- **Winding functions of the relators.** Computed from the definitions:
  - `W(R_1) = -s^-2 + s^-1 t^-1 - s^-1`;
  - `W(R_2) = -s^-3 + s^-2 t^-1 - s^-2 + s^-1 t^-1 - s^-1`;
  - `W(c) = -1`.
- **Bézout.** With `P = (a^2 R_1 a^-2)(a R_1 a^-1)(a^2 R_2 a^-2)^-1`,
  `W(P) = s^2 W(R_1) + s W(R_1) - s^2 W(R_2)`. Expanding:
  - `s^2 W(R_1) = -1 + s t^-1 - s`;
  - `s W(R_1) = -s^-1 + t^-1 - 1`;
  - `-s^2 W(R_2) = s^-1 - t^-1 + 1 - s t^-1 + s`.

  The sum is `-1 = W(c)`.
- **Conclusion.** So `u_2 := c P^-1 ∈ F_2'` has `W(u_2) = 0`, hence both Fox derivatives vanish, and
  `u_2 ∈ F_2''` by step 0.
- **Checks.** Free reduction of `c P^-1` gives the 34-letter word in the claim, and `c = u_2 P` holds
  letter by letter. Both Fox derivatives of the reduced word were recomputed as `0` exactly
  (`u2_check.py`). Independently, `c` and `P` have the same image in the faithful Magnus representation
  of `F_2/F_2''` (`metab_check.py`).

**2. Item 1.** Evaluation `w ↦ w(A,B)` is a homomorphism `F_2 → Sym(n)`, since a word acts last letter
first. If `G = <A,B>` is metabelian, then `F_2''` maps into `G'' = 1`, so `u_2(A,B) = 1` and
`c(A,B) = P(A,B)`. The metric `d` is bi-invariant, so `d(XY,1) ≤ d(X,1) + d(Y,1)`,
`d(UXU^-1,1) = d(X,1)` and `d(X^-1,1) = d(X,1)`. Hence

`t = d(c(A,B),1) ≤ d(R_1,1) + d(R_1,1) + d(R_2,1) = 2 D_1 + D_2 ≤ 3D`, and `2D_1 + D_2 ≤ 2 D_+`.

For an arbitrary pair, `c(A,B) = u_2(A,B) P(A,B)` gives item 2's inequality the same way.

**3. Item 3 (sharpness).**
- **Recounts.** The four certificate pairs are in
  `research/artifacts/hl-f-skew-product-rate-2026-09-14-search/`. They were recounted by `u2_check.py`
  and independently by `analyze.py` of `hl-f-sofic-relator-instability`; both give the table's
  `m_1, m_2, m_c`, and each row has `m_c = 2 m_1 + m_2`.
- **Groups.** The group orders and structures of `cert.x12` and `cert.s10` are GAP 4.13.1 output
  (`certgroups.g`, `certgroups.log`). The two skew products are abelian-by-abelian by construction:
  - the torus pair acts by `(x, y, i) ↦ (x+1, y, i + c(x,y))` and `(x, y, i) ↦ (x, y+1, i + d(x,y))`
    on `Z/3 × Z/3 × Z/2`, with `c` and `d` in the artifact;
  - the imprimitive pair lies in `Z/2 wr Z/5`.
- **Search.** The torus minimum `4/12` and the wreath minimum sum ratio `4/8` are exhaustive over their
  families (`metab_certs.py`).

**4. Item 4 (minimality).**
- **Reformulation.** A product of `N` conjugates of `R_j^±1` congruent to `c` modulo `F_2''` gives, by
  step 0, `P_1 W(R_1) + P_2 W(R_2) = -1` with `‖P_1‖_1 + ‖P_2‖_1 ≤ N`, where `‖·‖_1` is the sum of
  absolute coefficients.
- **Factorization.** Put `u = s^-1`, `v = t^-1`. Then `W(R_1) = -u f` with `f = 1 + u - v`, and
  `W(R_2) = -u g` with `g = 1 + u + u^2 - v - uv = (1 + u) f - u`.
- **Units.** The units of the Laurent polynomial ring `Z[Z^2]` are `±` monomials (compare leading terms
  in each variable).
- **Cases.**
  - `N ≤ 2`, one relator: `-1 = P_j W(R_j)` makes `f` or `g` a unit, but they have 3 and 5 terms.
  - `N = 2`, one conjugate of each: `±m_1 W(R_1) ± m_2 W(R_2)` with monomials `m_i` has at least
    `5 - 3 = 2` nonzero terms, so it is not `-1`.

  Hence `N ≥ 3`. ∎
