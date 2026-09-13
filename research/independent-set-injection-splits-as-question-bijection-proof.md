---
rg: 2
id: independent-set-injection-splits-as-question-bijection-proof
kind: route
title: Sum the independent-set rows over answers and over questions, and use faithful-trace counting for the column sums
target: independent-set-injection-splits-as-question-bijection
requires: []
---

Notation as in the target.  Two facts are used throughout.

- **(F0)** For projections `p, r` in `(M, tau)`, `tau(pr) = ||pr||_2^2`, so
  `pr = 0` iff `tau(pr) = 0`; and `pr = 0` iff `rp = 0`, by taking adjoints.
- **(F1) The rule of `I`.**  For `i != j`, `P_i^v P_j^w = 0` whenever `v = w`
  or `v ~ w`.  Within one row, `P_i^v P_i^w = 0` for `v != w`.  Since `G` is
  synchronous, `(q,a)` and `(q,a')` are adjacent for `a != a'`.  So for
  `i != j` and any `a, a'`:

  ```text
  P_i^(q,a) P_j^(q,a') = 0.                                        (P1)
  ```

**(IS1).**

1. **`W` has projection entries and unit row sums.**  `W_(iq)` is a sum of
   orthogonal projections from the PVM of row `i`, so it is a projection.
   `sum_q W_(iq) = sum_v P_i^v = 1`.
2. **Columns are orthogonal.**  For `i != j`,
   `W_(iq) W_(jq) = sum_(a,a') P_i^(q,a) P_j^(q,a') = 0` by (P1).  So
   `C_q = sum_i W_(iq)` is a projection.
3. **Column sums are one.**  `sum_q C_q = sum_i sum_q W_(iq) = t 1 = |Q| 1`.
   Taking traces, `sum_q tau(C_q) = |Q|` with `tau(C_q) <= 1`.  So
   `tau(1 - C_q) = 0`, and `C_q = 1` by faithfulness.  Thus `W` is a magic
   unitary.
4. **`(P_q^a)` is a PVM for each `q`.**
   - `P_q^a P_q^a' = sum_(i,j) P_i^(q,a) P_j^(q,a')`.
   - The terms with `i != j` vanish by (P1).
   - The terms with `i = j` give `delta_(aa') P_i^(q,a)`.
   - So the `P_q^a` are orthogonal projections, and
     `sum_a P_q^a = sum_i W_(iq) = C_q = 1`.

   This is the MSSV computation.
5. **Perfection for `G`.**  Let `V(q,q';a,a') = 0`.  Then `(q,a) != (q',a')`
   by the deletion convention, so the two vertices are adjacent.
   - `P_q^a P_(q')^(a') = sum_(i,j) P_i^(q,a) P_j^(q',a')`.
   - Terms with `i != j` vanish by the rule of `I`.
   - Terms with `i = j` vanish by row orthogonality.
6. **(ISB1).**
   - `P_q^a W_(iq) = sum_j sum_(a') P_j^(q,a) P_i^(q,a')`.
   - Terms with `j != i` vanish by (P1).
   - Terms with `j = i` give `P_i^(q,a)`.
   - The same computation gives `W_(iq) P_q^a = P_i^(q,a)`.  Hence `W_(iq)`
     and `P_q^a` commute.

**(IS2).**

- **Projections and rows.**  `W_(iq)` and `P_q^a` are commuting projections,
  so `P_i^(q,a) = W_(iq) P_q^a` is a projection.  For fixed `i` these are
  mutually orthogonal, and `sum_(q,a) W_(iq) P_q^a = sum_q W_(iq) = 1`.
- **Same vertex, `i != j`.**
  `W_(iq) P_q^a W_(jq) P_q^a = W_(iq) W_(jq) P_q^a = 0`, since `W_(jq)`
  commutes with `P_q^a` and the columns of `W` are orthogonal.
- **Adjacent, same question.**  With `q = q'` and `a != a'`,
  `W_(iq) W_(jq) P_q^a P_q^a' = 0`.
- **Adjacent, `q != q'`.**
  - `V(q,q';a,a') = 0` or `V(q',q;a',a) = 0`.
  - The model of `G` gives `P_q^a P_(q')^(a') = 0` in the first case, and by
    (F0) also in the second.
  - Using `P_(q')^(a') W_(jq') = W_(jq') P_(q')^(a')`, we get
    `W_(iq) P_q^a W_(jq') P_(q')^(a') = W_(iq) (P_q^a P_(q')^(a')) W_(jq') = 0`.

**(IS3).**

- **From `G` to `I`.**  Given a perfect `R^U` model of `G`, label `[t] = Q`
  and take `W_(iq) = delta_(iq)`.  (IS2) then gives a perfect `R^U` model of
  `I`.
- **From `I` to `G`.**  Given a perfect `R^U` model of `I`, steps 1--5 run
  inside `R^U` with its faithful trace.  They give a perfect `R^U` model of
  `G`.
