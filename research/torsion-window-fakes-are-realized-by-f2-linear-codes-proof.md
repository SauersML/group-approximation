---
rg: 2
id: torsion-window-fakes-are-realized-by-f2-linear-codes-proof
kind: route
title: Write down two rank-five F_2-linear codewords on three six-bit sites and check all thirty-one ranks
target: torsion-window-fakes-are-realized-by-f2-linear-codes
requires:
  - minimal-window-shannon-derivations-miss-rokhlin-domination
artifacts:
  - experiments/entropic-window-fakes-2026-09-17/verify_linear.py
  - experiments/entropic-window-fakes-2026-09-17/z3_rep.json
---
1. **Reduction to `Z/3`.** This is step 1 of `minimal-window-shannon-fake-on-a-cyclic-orbit`. All sites `X = <t>`
   and all translations between sites lie in `<t>`, so the premises (I), (D), (T) are the same in `G` as in `Z/3`.
   Write `x_0, x_1, x_2` for `x_1, x_t, x_(t^2)` and `y_0, y_1` for `y_1, y_t`. Since `E = <t>`, (D) only says
   that `y_0` and `y_1` are functions of `(x_0, x_1, x_2)`.

2. **The realization.** Take `V = F_2^18 = B_0 ⊕ B_1 ⊕ B_2`, with bases `e_1..e_6`, `f_1..f_6` and `g_1..g_6`.
   Let `x = (x_0, x_1, x_2)` be uniform on `V`, so `x_i` is its `B_i`-coordinate. A subspace `U ⊆ V*` of linear
   functionals defines the random variable `U(x)`, with entropy `dim U` bits. For a family of such variables, the
   joint entropy is the dimension of the sum of their spaces. Take the spaces `B_i*` for `x_i` (identifying
   `V* = V` through the basis) and:

       W_0 = span( e1,  g1,  e2+f1+g2,  e3+f2+g3,  e2+f3+g3 )
       W_1 = span( e4,  f2+f3,  g1+e5,  f1+g2+e6,  f2+g3+e4+e5 )

3. **Ranks.** Put `h(S) = dim(sum of the spaces in S) / 6`. By direct Gaussian elimination over `F_2`, the table is
   exactly the polymatroid of artifact Section 4 of `research/artifacts/shannon-window-certificates-2026-09-17.md`:
   - `h(x_i) = 1`, `h(x_i x_j) = 2`, `h(x_0 x_1 x_2) = 3`;
   - `h(y_j) = 5/6`, `h(y_0 y_1) = 5/3`;
   - `h(x_0 y_0) = h(x_0 y_1) = h(x_1 y_1) = h(x_2 y_0) = 5/3`, and `h(x_1 y_0) = h(x_2 y_1) = 11/6`;
   - `h(x_0 y_0 y_1) = 5/3`, and every other triple `= 5/2`;
   - `h(x_0 x_1 x_2 y_j) = 3`, `h(x_1 x_2 y_0 y_1) = 3`, `h(x_0 x_1 y_0 y_1) = h(x_0 x_2 y_0 y_1) = 5/2`;
   - `h(all five) = 3`.

   Hand check of the key entries:
   - `W_0 ∩ W_1 = 0`, and `W_0 + W_1 ⊇ B_0`. It contains `e1`, `e4`, `e5 = g1 + (g1+e5)`, and
     `e2+e6 = (e2+f1+g2) + (f1+g2+e6)`. It also contains `e3+e4+e5 = (e3+f2+g3) + (f2+g3+e4+e5)`, hence `e3`.
     With `e2+e3 = (e3+f2+g3) + (e2+f3+g3) + (f2+f3)` it contains `e2`, and then `e6`. So `h(x_0 y_0 y_1) = h(y_0 y_1) = 10/6`.
   - `W_0 ∩ B_1 = 0`. Take `a e1 + b g1 + c_1 w_1 + c_2 w_2 + c_3 w_3` in `B_1`, where `w_1, w_2, w_3` are the
     last three generators. The `B_0`-part `a e1 + (c_1+c_3) e2 + c_2 e3` must vanish, and so must the `B_2`-part
     `b g1 + c_1 g2 + (c_2+c_3) g3`. That forces all coefficients to 0. So `h(x_1 y_0) = 11/6`.
   - `W_1 ∩ B_2 = 0`. For `a e4 + b(f2+f3) + c_1(g1+e5) + c_2(f1+g2+e6) + c_3(f2+g3+e4+e5)`, the vanishing
     `B_1`-part forces `c_2 = b = c_3 = 0`, and then the vanishing `B_0`-part forces `a = c_1 = 0`. So `h(x_2 y_1) = 11/6`.

   `verify_linear.py` recomputes all ranks. It checks (I), the support condition (D), and all 30 translation
   equalities (T) under `t = +1, +2`, in integer arithmetic:

       cd experiments/entropic-window-fakes-2026-09-17 && python3 verify_linear.py 3 0,1,2 0,1 z3_rep.json
       -> ground set 5, block size d=6, 30 translation equalities checked, all ranks exact
          rank(y_f) = [5, 5]  Phi = 5/6
          ALL EXACT   (exit 0)

4. **Objective.** `Phi = h(y_0) + h(x_0 y_0 y_1) - h(y_0 y_1) = 5/6 + 5/3 - 5/3 = 5/6`.

5. **No derivation.** The `x_i` are independent and uniform with `H(x_i) = 1` (6 bits), so (I) holds. (D) holds
   because `y_j` is a function of `x`. (T) holds by step 3. Any valid information inequality holds for this entropy
   vector, because it is the vector of genuine random variables. So a derivation of `Phi >= 1` from (I), (D), (T)
   and valid information inequalities would give `5/6 >= 1`.

6. **Where the realization stops being a configuration.** A genuine configuration has `y_1 = psi(x_1, x_2, x_0)`, so
   its functional space would be the shift `σ(W_0)` under `σ: B_0 → B_1 → B_2 → B_0`. But `e1 ∈ W_0` and `σ(e1) = f1 ∉ W_1`:
   a combination with `B_1`-part `f1` uses `f1+g2+e6` and not `f2+f3` or `f2+g3+e4+e5`, so it has a nonzero `g2`-part. So the realization
   is not a genuine `psi`, and the true inequality `Phi >= 1` for `Z/3` codes is not contradicted.
