---
rg: 2
id: gupta-torsion-element-survives-modulo-gamma-seven-citation
kind: route
title: Import Gupta--Levin 1986 Lemma 2.2 (after C. K. Gupta 1973) and Lemma 4.4
target: gupta-torsion-element-survives-modulo-gamma-seven
requires: []
---

**Source.** C. K. Gupta and F. Levin, "Dimension subgroups of free center-by-metabelian
groups", Illinois J. Math. 30 (1986), no. 2, 258–273. Read on 2026-09-18 from the
Project Euclid PDF, pp. 258–267.

**Notation (p. 258).**
- `f = Δ(F)`, `a = ZF(F' − 1)`, `r = ZF(R − 1)`, with `R = [F'', F]`.
- `1 + X` denotes the group elements `w` with `w − 1 ∈ X`.

**Imports.**
- **The element (p. 260, (i)).** "`K_6(F)` is the fully invariant closure of `u_6`",
  displayed as the product over `τ` of `[f_{1τ}, f_{2τ}; f_{1τ}, f_{2τ}, f_{3τ}, f_{4τ}]`,
  times six further terms. Here `[g_1, g_2; g_3, g_4] = [[g_1, g_2], [g_3, g_4]]`.
- **Hurley's representation (p. 259).** `θ: f_i ↦ 1 + x_i` into the units of
  `P = Z[[y_1, y_2, …]]/C`, "with Ker θ = faf". The units of `P` form a
  centre-by-metabelian group (Hurley).
- **Lemma 2.2 (p. 261), credited to C. K. Gupta [1]:**
  - "(i) `F ∩ (1 + faf) = K_6(F) · [F'', F]`";
  - "(ii) `K_6(F) ⊆ [F'', F]` if and only if rank `F ≤ 3`";
  - "(iii) `u^2 ∈ [F'', F]` for all `u ∈ K_6(F)`".
- **Lemma 4.4 (p. 266):** "Let `u ∈ U_6(F)` and suppose that `u` is a nontrivial product
  of terms `[f_{i,1}, f_{i,2}; f_{i,1}, f_{i,2}, f_{i,3}, f_{i,4}]` with `f_{i,3} ≠ f_{i,4}`,
  each term occuring at most once. Then `u ∉ 1 + r + f^7`. In particular,
  `K_6(F) ⊄ 1 + r + f^7`." The proof (pp. 266–267) was read but not re-checked line by line.

**Derivation of the claim.** In Gupta–Levin, `F` is free on `f_1, f_2, ...`. Let
`π: F -> F_4` be the retraction fixing `f_1, ..., f_4` and killing the other generators.
It fixes `u_6` and maps `[F'', F]` into `[F_4'', F_4]`.
1. **Square.** By (iii), `u_6^2 ∈ [F'', F]`. Applying `π` gives `u_6^2 ∈ [F_4'', F_4]`.
2. **Not in `[F'',F]γ_7`.** The subgroup `[F'', F] γ_7(F)` lies inside `1 + r + f^7`:
   - `w ∈ [F'', F]` gives `w − 1 ∈ r`, and `w ∈ γ_7(F)` gives `w − 1 ∈ f^7`;
   - `ab − 1 = (a−1)(b−1) + (a−1) + (b−1)`, and `r` is an ideal.

   This subgroup is also fully invariant. So `u_6 ∈ [F'', F] γ_7(F)` would put all of
   `K_6(F)` inside `1 + r + f^7`, contradicting Lemma 4.4.
3. **Rank 4.** Since `[F_4'', F_4] γ_7(F_4) ⊆ [F'', F] γ_7(F)`, we get
   `u_6 ∉ [F_4'', F_4] γ_7(F_4)`. In particular `u_6 ∉ [F_4'', F_4]`. ∎
