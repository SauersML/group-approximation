# EX review, second wave, quantum and L²: part 8. Verdicts on the seven established Kac nodes of ex2-kac-forbidden-pair and ex-kac-quantum-bijection

Lane `ex-verify2-quantum-l2`, 2026-09-13, at coordinator request. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Scope.**
- ex2-kac-forbidden-pair: the two established nodes (landings `a4fa6dc2d0`, `f8d52e7ee7`; report
  `ex/reports/ex2-kac-forbidden-pair.final.txt`).
- ex-kac-quantum-bijection: the five established nodes (landings `680bb7f6cc`, `1f5de8c39b`, `4b7646f007`,
  `158a58d361`, `a97f61f734`).

**Freshness.** Blobs were compared at `7d41d1a16a`, at `561fc1df60` and at the tip `87d04a8ce8`.
- No claim or proof route changed after the reviews cited below.
- The only change is `00051a8d3d`, which added the "equivalent form" bullet to
  `hidden-labels-import-cross-context-commutation` before my part 5 read it.

## 8.0 Verdicts

| node | lane | verdict | where |
|---|---|---|---|
| `forbidden-pair-splits-are-central-rectangle-splittings` | ex2-kac-forbidden-pair | **PASS** | part 5 §5.2; MSSV Def. 2.7 and Thm 3.1 and Lin Def. 3.15 checked at source |
| `fibre-commutative-quantum-isomorphisms-are-coset-systems` | ex2-kac-forbidden-pair | **PASS** | part 5 §5.3 |
| `independent-set-injection-splits-as-question-bijection` | ex-kac-quantum-bijection | **PASS** | §8.1 |
| `coset-systems-are-torsor-isomorphism-games` | ex-kac-quantum-bijection | **PASS** | T1: (LT) and (P0)–(P5) re-derived in part 7 §7.1. T2–T4: part 7 §7.1 |
| `coset-refinement-forces-rectangular-central-splitting` | ex-kac-quantum-bijection | **PASS** | §8.2 |
| `exact-label-coset-refinements-are-affine` | ex-kac-quantum-bijection | **PASS** | EL1–EL3 and the consequence: part 7 §7.2 |
| `hidden-labels-import-cross-context-commutation` | ex-kac-quantum-bijection | **PASS**; one justification in (H7) repaired forward | §8.3 |

**No FAIL.** None of these nodes decides a famous problem. The open roots
`non-group-dual-colored-qc-qa-pair-exists` and `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`
still compute OPEN.

## 8.1 `independent-set-injection-splits-as-question-bijection`: PASS

- **(P1).** Synchronicity makes `(q,a) ~ (q,a')` for `a != a'`. So for `i != j`,
  `P_i^(q,a) P_j^(q,a') = 0`, whether `a = a'` or not.
- **IS1.**
  - The `W_(iq)` are projections with row sums `1`.
  - The columns are orthogonal by (P1), so `C_q = sum_i W_(iq)` is a projection.
  - `sum_q C_q = t 1 = |Q| 1` and `τ(C_q) <= 1` give `τ(C_q) = 1`. So `C_q = 1` by faithfulness, and `W`
    is a magic unitary.
  - `P_q^a` is a sum of mutually orthogonal projections, and `sum_a P_q^a = C_q = 1`.
  - Perfection: on a forbidden pair the vertices are distinct and adjacent. So the `i != j` terms vanish by
    the rule, and the `i = j` terms by row orthogonality.
  - (ISB1): the `j != i` terms of `P_q^a W_(iq)` vanish by (P1), leaving `P_i^(q,a)`; symmetrically on the
    other side.
- **IS2.**
  - Row orthogonality for `q != q'`: move `P_q^a` left past `W_(iq)` and `P_(q')^(a')` right past `W_(iq')`.
    Then `W_(iq) W_(iq') = 0`.
  - Same vertex, `i != j`: `W_(iq) W_(jq) P_q^a = 0`.
  - Adjacent across questions: `W_(iq) (P_q^a P_(q')^(a')) W_(jq') = 0`, using perfection and (F0).
- **IS3.** Take `W = 1` in one direction, and run IS1 inside `R^U` in the other.
- **Credit.** The node reads the proof of MSSV Thm 3.1 at source. I checked only the statement (l. 724).

## 8.2 `coset-refinement-forces-rectangular-central-splitting`: PASS

- **Pushforward.** For `(a,a') notin Acc`, every `(s,s')` with `β(s) = a` and `β(s') = a'` lies off `cD`,
  so (CS) kills it. So `A(G) -> A(R)` is a unital *-homomorphism.
- **(R1).** `c d_1 (c d_2)^-1 c d_3 = c d_1 d_2^-1 d_3 in cD`. So components are complete bipartite, with
  disjoint sides.
- **(R2)–(R3).** A fibre point in no block has `p^s = 0`. `z_i p_(q')^(s') = 0` off `B'_i`, so
  `z_i = z_i z'_i`, and adjoints give `z_i = z'_i`.
- **(R4)–(R5).**
  - `z_i` lies in `W*(p_q) ∩ W*(p_(q'))`, so `z_i in N' ∩ M`.
  - The used sets satisfy `U_q(z_i) x U_(q')(z_i) ⊆ (β x β')(cD) ⊆ Acc`.
- **(R6).**
  - For `z in N'`, the projection onto `[N' z H]` is invariant under `N'` and `N`, so it lies in `Z(N)`.
  - For `x in N`, `xz = 0` iff `x C(z) = 0`, so the used sets are unchanged.
  - The `f_T` partition unity centrally, and `f_T <= C(z_i)` for `i in T` gives (RCS).
- **Corollaries.**
  - Three-colourings: two disjoint nonempty subsets of `{1,2,3}`, so one is a singleton, giving
    commutation piecewise.
  - Label-matching presentations: the (R3) argument.
  - Without padding: `s_0 <S^-1 S>` is a coset containing `S`. Factoring forces
    `S^-1 S ⊆ D`, hence `s_0 <S^-1 S> ⊆ cD ⊆ Acc`.
- **Model test.**
  - `f_1, f_2, f_3` are orthonormal, since `(e_2 - e_3)·(e_2 + e_3) = 0` and `||(e_2 - e_3)/sqrt2|| = 1`.
    `e_1 ⊥ f_1`, so the model is perfect.
  - Irreducibility, by hand: every span of basis vectors is moved by some `f`-projection. So the pair
    generates `M_3`.
  - Corollary 1 then forces `(1,1) in Acc`, which it is not.

## 8.3 `hidden-labels-import-cross-context-commutation`: PASS, with a justification repaired

- **(H1).** Goursat blocks give labels `ℓ_e`. The block sums `[ℓ_e = λ]` lie in `W*(p_c) ∩ W*(p_(c_e))` by
  (R3). Shared variables are functions `ψ_e^v` of the label.
- **(H2).** `S_c = s_c K~`. With `N_e` normal, `ℓ_e(s_c k) = (x_0 N_e)(k N_e)`, so the joint label image is a
  coset `(g', g'') T`.
- **(H3).** Goursat for `T` splits the coset into rectangles `C'_j x C''_j`, with disjoint sides. For
  `s in S_c`, `ℓ_(e')(s) in C'_j` iff `ℓ_(e'')(s) in C''_j`. So `m_j` has both block-sum expressions, lies in
  three abelian algebras, and `sum m_j = 1`.
- **(H4).** Every label pair in a rectangle comes from some `s in S_c`. So `U_j x W_j` sits inside the
  restriction of `Allowed_c` to `(u,w)`, and a rectangle missing a pattern has a singleton side.
- **(H5).**
  - For `j in J_u`, `X_u m_j = ± m_j`, so `X_u m in W*(p_(c''))`, and `[X_u, P_(c'')^b] m = [X_u m, P^b] = 0`.
  - Symmetrically on `1 - m`.
- **(H6).** `m in N' ∩ M`, `x m = 0` gives `x C(m) = 0`, and a factor forces `C(m) in {0,1}`. The
  contradiction follows.
- **(H7): the repaired justification.**
  - The factor-pair bullet said: "a projection of `W*(P_q, P_(q'))` that commutes with both PVMs is central,
    hence `0` or `1`". Here `m` is a sum of refined block projections, and with padding it need not lie in
    the pair algebra `N`. So the sentence did not apply to it.
  - The conclusion is right, by (H6). If `C(m) = 1`, (HL) on `m` makes `P_q^a` commute with `P_(q')`, so it is
    central, hence `0` or `1`. If `C(m) = 0`, then `m = 0`, and (HL) on `1` does the same for `P_(q')^(a')`.
  - Corrected forward in `hidden-labels-import-cross-context-commutation-proof`.
- **(H8), model test.**
  - Perfection holds: `X_y` swaps two vectors with the same `u`-bit, `X_z` two with the same `w`-bit, and
    the joint spectrum of `(X_u, X_w)` is NAND.
  - `X_u` and `X_w` separate the basis, and the transpositions give `M_3`.
  - `[X_u, X_z] != 0` and `[X_w, X_y] != 0`.
