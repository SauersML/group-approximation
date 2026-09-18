# Referee report (gq-referee-a, proof-gap lens): GL_n(Q) in E_(n+1) of a finitely presented ring

**Reviewed:** `gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring` and its route `-proof` (lane gq-ring-fp-simple,
7bbbef172), read on origin/main.

**Verdict: PASS.** No gaps found.

- **Steps 1–3.** Correct.
  - `Ψ(g) = φ(g) + (1−E)I_m` is multiplicative, because the entries of `φ(g)` lie in `ERE`.
  - `Ψ` is injective, and `Ψ(e_ij(q)) = e_ij(φ(q))`.
  - `SL_m(Q) = E_m(Q)`, and `GL_n(Q) ↪ SL_{n+1}(Q)`.
- **Step 4.** Correct. For `m ≥ 3`, the set of `r` with `e_ij(r) ∈ H` is additive. Closure under
  products follows from `[e_ik(x), e_kj(w')] = e_ij(xw')`, using a free third index. So every
  `Z`-combination of words in the generators is reached.
- **Step 5.** Correct: `ρ(φ(q)) = q ρ(E)` with `ρ(E) ≠ 0`.
- **Step 6 (word problem in the model).** Correct.
  - For each offset `c`, the `c`-th diagonal of `Σ S^a d_{ab} T^b` has entries
    `Σ_{a−b=c} [k ≥ b] d_{ab}(k−b)`.
  - Each entry function is eventually rational in `k`, apart from finitely many exceptional values.
  - Vanishing is therefore decidable.
- **Scope.** The claim that the group has solvable word problem is made only for the model group
  `E_{n+1}(ρ(R_T))`. That is correct as stated.
- **Superseded remark.** The "Relevance" bullet, which says Problem 2.7 needs `K_2` control of `R_T`, is
  superseded for rings with a Leavitt pair. See the reviewed Steinberg lemmas (fbbb1c736, d45def137),
  which apply to `R_L`, `R_Q` and `D`. `R_T` itself has no Leavitt pair, so the remark still stands for
  `R_T`.
