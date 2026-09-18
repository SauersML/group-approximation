# Referee report (gq-referee-a, proof-gap lens): referee-c's direct proof that St_n(R) is finitely presented, n >= 5

**Reviewed:** `research/artifacts/gq-referee-c-steinberg-finite-presentation-and-kazhdan-theorem.md` (5d6390c47),
§§2, 4 and 5.

**Verdict: PASS.** No gaps found. For every finitely presented unital ring `R` and every `n ≥ 5`, `St_n(R)` is
finitely presented, and the presentation is explicit. The proof uses only (R1)–(R3). It is now recorded as the
claim `steinberg-groups-of-fp-rings-are-fp-in-rank-five`.

## The identity (★)
Correct.
- `[x,z] = 1` gives `x[y,z]x^{-1} = [xyx^{-1}, z] = [uy, z]`.
- `[uy, z] = u[y,z]u^{-1}[u,z] = [y,z][u,z]`, since `u` commutes with `[y,z]`.
- `[y,z]` commutes with `u` and `z`, hence with `[u,z]`. So `[x,[y,z]] = [u,z]`.

## The induction H(L) ⇒ H(L+1)
- **Base case.** H(1) is (B1) and (B2). Correct: the monomial `1` has length 0, so (R2)_1 is exactly the three
  (B2) families.
- **(i) Independence of the intermediate index.** Correct. It uses four indices `i, j, k, k'`.
  - Inputs from H(L): `[X_ik(a), X_k'j(b)] = 1` (`k ≠ k'`, `i ≠ j`); `u = X_ik'(a)` and `[y,z] = X_kj(b)` by
    (R2)_L with one factor of length 0; `u` commutes with `X_kj(b)`; and `X_kj(b)` commutes with `X_k'j(b)`.
  - All the lengths involved are `≤ L`, because `|a|, |b| ≥ 1`.
- **(ii) Independence of the split.** Correct. It uses four indices `i, k, l, j`.
  - `X_kj(cb') = [X_kl(c), X_lj(b')]` holds by (R2)_L, since `|cb'| = |b| ≤ L`.
  - `u = X_il(ac)` is legitimate because `|ac| ≤ L`, which holds as `|b'| ≥ 1`.
  - Any two splits differ by one such move, so the value does not depend on the split.
- **(iii) (C/R3)_{L+1}: where the fifth index is needed.** Correct.
  - Why five: the index pairs `(i,j)` and `(k,l)` satisfy `j ≠ k` and `i ≠ l`, and can involve four distinct
    values. So `p ∉ {i,j,k,l}` needs `n ≥ 5`.
  - Checked commutations: `X_kl(m')` against `X_ip(a)` (`l ≠ i`, `k ≠ p`) and against `X_pj(b)` (`l ≠ p`, `k ≠ j`).
  - The case where both lengths are `L+1` reduces to the one-long case with a fresh `p' ∉ {i,j,k,p}`, which again
    needs 5 indices.
  - The case `(k,l) = (i,j)` is included.
- **(iv) (R2)_{L+1}.** Correct.
  - For `m' = 1`, (★) applies with `x = X_ip(a)`, `y = X_pj(b)`, `z = X_jk(1)`. Its hypotheses:
    - `[x,z] = 1`, since `p ≠ j` and `i ≠ k`;
    - `u = X_ij(m)` commutes with `X_pk(b)` by (iii);
    - `X_pk(b)` commutes with `X_jk(1)`.
  - The case `m = 1` is symmetric. It uses (iii) twice, for `X_ip(c)` against `X_jk(m')` and for `X_jk(m')`
    against `X_pk(b)`.
- **Ordering of the steps.** Well-definedness at `L+1` comes from (i) and (ii), which use H(L) only. Then (iii)
  and (iv) use it. The order is consistent.

## The conclusion
- **φ respects the relations.** Correct.
  - (R1): for fixed `(i,j)` the `X_ij(m)` commute, by (C) with `(k,l) = (i,j)`.
  - (R3): the factors commute pairwise.
  - (R2) is bilinear. `X_ik(·)` commutes with every `X_ij(·)` and every `X_jk(·)`, so all commutators of factors
    are central in the subgroup they generate. Hence `[∏X, ∏Y] = ∏[X,Y]`.
- **ψ inverts φ.** `ψ(X_ij(m)) = x_ij(m)` by (R2) in `St_n(F)`. Both composites are the identity on generators.
- **Quotient step (§4).** Correct. For distinct `i, k, l, j`, `x_ij(aρb) = [x_ik(a), [x_kl(ρ), x_lj(b)]]`, and the
  elements `aρ_t b` span `I` additively.
- **Rank 5 in the one-group statement (§5).** Correct, conditional on C1–C4. Step (a) needs `5 ≥ sr + 2` and
  `5k ≥ 5`, and steps (b)–(e) do not depend on the rank.

## Consequence for Problem 2.7
- Every Steinberg-group route of rank `≥ 5` now has a citation-free finite presentation:
  - `St_{6n+7}(R_L)`;
  - `St_10(S)` of `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` (proof-gap PASS, d45def137), for
    `S = R_L, D, R_Q`;
  - `St_5(D)`, which still depends on C1–C4.
- The citation-free single group is `St_10(S)`: finitely presented by this node, and containing every `GL_n(Q)`
  by the d45def137 lemma.
- Only property (T) still rests on the Ershov–Jaikin-Zapirain import, and Problem 2.7 does not need it.
