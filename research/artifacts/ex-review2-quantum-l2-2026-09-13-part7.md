# EX review, second wave, quantum and L²: part 7. Coset-system quantum symmetry (T2–T4) and exact-label affinity (EL2–EL3), which earlier reviews had checked only at node level

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Why.** ex-verify-logic-quantum re-derived T1 of `coset-systems-are-torsor-isomorphism-games` and EL1 of
`exact-label-coset-refinements-are-affine`, and checked the remaining items at node level only. These are
two of the five kac-quantum firewalls of brief item (d).

## 7.0 Verdicts

| claim | items | verdict |
|---|---|---|
| `coset-systems-are-torsor-isomorphism-games` (+ `-proof`) | T2, T3, T4 (T1 already PASS) | PASS |
| `exact-label-coset-refinements-are-affine` (+ `-proof`) | EL2, EL3 and the consequence (EL1 already PASS) | PASS |
| ex-lueck-approximation post-review edit `2686fb6869` | Theorem D nonempty, countability dropped, irrational-node wording | wording only; consistent with backlog part 1 |

## 7.1 Coset systems: T2–T4

- **(LT) and (P1), re-derived.** Entries across fibres vanish, since diagonal colours differ. In a fibre,
  `v_((q,x),(q,a)) v_((q,e),(q,b)) != 0` forces `b = a x^-1`. Summing rows gives `A = AB` and `B = BA`, so
  `A = A^* = (AB)^* = BA = B`.
- **T2.** Take `O(Qut X(S_1)) = A(Iso(X(S_1), X(S_1)))`, with `Δ(u_(yw)) = sum_z u_(yz) ⊗ u_(zw)`.
  - With `p^s = u_((q,e),(q,s))`, only `z = (q,r)` survives, and (LT) gives
    `Δ(p^s) = sum_r p^r ⊗ p^(s r^-1)`.
  - `ε(p^s) = δ_(s,e)` and `S(p^s) = u_((q,s),(q,e)) = p^(s^-1)`.
- **T3.**
  - Nonzero members of a PVM are linearly independent, so the nonzero `p^r ⊗ p^t` are independent.
  - For `r, t in L_q`, `Δ(p^(tr))` contains `p^r ⊗ p^t != 0`, so `p^(tr) != 0`. `e in L_q` because
    `ε(p^e) = 1`. In a finite group, closure under products is enough.
  - `σ in Sol_0` gives the character `p^s -> δ_(s,σ_q)`, since (CS) with `c = 1` is `(σ_q, σ_(q')) in D`.
  - **Non-cocommutativity.** The flip of `Δ(p^s)` is `sum_(r') p^(r') ⊗ p^(r'^-1 s)`. If `s, r' in L_q`
    with `s r'^-1 != r'^-1 s`, the nonzero terms `p^(r') ⊗ p^(s r'^-1)` and `p^(r') ⊗ p^(r'^-1 s)` are
    distinct independent members. So `Δ != flip ∘ Δ`, and `Qut X(S_1)` is not dual to a discrete group.
- **T4.**
  - The qc/qa separation is T1.
  - The Kac, non-Connes-embeddable Haar algebra is `closure-safe-support-is-exactly-the-colored-iso-rung`
    (logic-quantum part 2, PASS).
  - Setting the cross blocks of the magic unitary of `Z` to `0` generates a Hopf *-ideal, and the quotient
    maps onto `O(Qut X(S_1))` through the `X(S_1)` block.
  - Quotients of cocommutative Hopf algebras are cocommutative, so by T3 `Qut Z` is not a group dual.

## 7.2 Exact-label refinements: EL2–EL3

- **(G), (S1).**
  - Goursat's lemma gives the blocks `c_1 x N × c_2 θ(xN)`.
  - Acceptance on a block makes `x_v ∘ β_c` constant on its first factor. Label exactness then gives at
    most two blocks, `[K_1 : N] <= 2`, and (A1) `x_v(β_c(c_1 x)) = χ_v(x) + b_v`.
- **(S2).** For `s notin c_1 K_1`, summing (CS) over `s'` gives `p_c^s = 0`. The support is an intersection
  of left cosets, nonempty because `sum p = 1`.
- **(S3).** For `k in K~_c ⊆ K_1^(c')` and each `v in sh(c)` (with `c ∩ c' = {v}` on single-variable edges),
  `Φ_c(s_c k) = χ(k) + b'`. So `A_c` is affine, and its points restrict allowed assignments.
- **(S4) EL2.**
  - Put `P_i = sum over B_i of p_c^s` and `P'_i = sum over B'_i of p_(c')^(s')`.
  - (CS) gives `P_i P'_j = 0` for `i != j`, and both families sum to `1` by (S2). Hence
    `P_i = P_i P'_i = P'_i`, algebraically.
  - Each block carries one value of `v`, so `X_v^(c) = X_v^(c')`. The `X_v^(c)` for `v in sh(c)` are
    functions of one PVM and commute, and their joint spectrum lies in `Φ_c(S_c) = A_c`.
- **(S5) EL3.**
  - `Q_c^a -> sum over Φ_c(s) = a of p_c^s` is a PVM over `A_c`, since the support is `S_c`. Agreement on
    shared variables is EL2. So the map is a unital *-homomorphism.
  - For an `R^U` model `(Q)`, choose completions `κ_c(a) in Allowed_c` by EL1 and put
    `P_c^w = sum over κ_c(a) = w of Q_c^a`. Contexts overlap only in shared variables, where the `Q`
    agree, so the `P` form a perfect `R^U` model of `G_B`.
- **Consequence.**
  - A trace on `A(R)` composed with the pushforward is a perfect tracial model of `G_(B_R)`. An `R^U` model
    of `G_(B_R)` would lift, so there is none.
  - The step to a nonhyperlinear group uses the established `locally-affine-support-bcs-is-exactly-the-lcs-boundary`
    and `lcs-tracial-ru-gap-equiv-nonhyperlinear`. Neither is re-derived here.

## 7.3 The Lück edit `2686fb6869`

It changes three files, all in wording:
- Theorem D and Proposition 3.1 now require `X` nonempty, which `H_0(X; Z) = Z` needs.
- Countability is dropped from the survey import, as backlog checked for Theorem 6.4.
- The irrational node now says what `R^x` refutes: the rationality form of Atiyah's question, not strong
  Atiyah. `R^x` has no bound on the orders of its finite subgroups.

No new mathematics was added, so no further review is needed.
