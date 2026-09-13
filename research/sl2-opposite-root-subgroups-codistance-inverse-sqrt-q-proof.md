---
rg: 2
id: sl2-opposite-root-subgroups-codistance-inverse-sqrt-q-proof
kind: route
title: The root coset graph of SL_2(q) is the determinant-one incidence on nonzero vectors, whose Gram operator is explicit
target: sl2-opposite-root-subgroups-codistance-inverse-sqrt-q
requires: [coset-graph-singular-values-bound-fixed-space-angles]
---

**Model.** `U_+ = Stab_G(e_1)` and `U_- = Stab_G(e_2)`, and `G` is transitive on `k^2 \ 0`.
- `gU_+ ↦ g e_1` and `gU_- ↦ g e_2` identify both sides of `Γ` with `k^2 \ 0`.
- The edge `g` joins `g e_1` to `g e_2`. A pair `(v, w)` comes from an element iff `det[v | w] = 1`, and
  then from exactly one element.
- So `v ~ w` iff `det(v, w) = 1`. Each `v` has the `q` neighbours on an affine line.

**The Gram operator.** `(MM^T)(v, v')` counts the `w` with `det(v,w) = det(v',w) = 1`.
- If `v' = v`, the count is `q`.
- If `v' = λv` with `λ ≠ 1`, it is `0`, because `det(v', w) = λ det(v, w)`.
- If `v, v'` are independent, it is `1`: two independent linear equations have one solution.

So `MM^T = qI + J - Σ_{λ ∈ k^*} P_λ`, where `J` is the all-ones matrix and `(P_λ f)(v) = f(λv)`. Here
`Σ_λ P_λ = (q-1)Π`, with `Π` the projection onto dilation-invariant functions, and `J`, `Π` commute.
- *Constants:* eigenvalue `q + (q^2 - 1) - (q - 1) = q^2`.
- *Dilation-invariant functions orthogonal to constants* (dimension `(q+1) - 1 = q`): eigenvalue
  `q - (q-1) = 1`.
- *Functions with `Πf = 0`* (dimension `q^2 - 1 - (q+1) = q^2 - q - 2`): eigenvalue `q`.

Both sides have degree `q`, so the singular values of `M/q` are `1`, `q^{-1/2}` and `q^{-1}`, with the
stated multiplicities. For `q >= 3`, `q^2 - q - 2 > 0`, so `σ_2 = q^{-1/2} < 1`, and `Γ` is connected.
This gives (b) and the regularity and connectivity in (a).

**Girth.** `Γ` is bipartite, and two distinct vertices on one side share at most one neighbour, so there
are no 4-cycles. Take `v_1 = e_1`, `v_2 = e_2`, `v_3 = e_1 + e_2`, which are pairwise independent, and let
`w_ij` be the unique common neighbour of `v_i, v_j`.
- If two of the `w_ij` coincide, say `w`, then `det(v_i, w) = 1` for all three `v_i`.
- The first two give `det(e_1 + e_2, w) = 2`, which is `0` in characteristic 2 and `2 ≠ 1` otherwise, a
  contradiction.

So `v_1 w_12 v_2 w_23 v_3 w_31` is a 6-cycle, and the girth is `6`. This completes (a).

**(c).** Apply `coset-graph-singular-values-bound-fixed-space-angles` with `A = G`, `H = U_+`, `K = U_-`.
By (a), `<U_+, U_-> = G`. ∎
