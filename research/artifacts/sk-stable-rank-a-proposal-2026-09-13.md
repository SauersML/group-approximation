# sk-stable-rank-a proposal: the stable-rank shortcut proposes no text (2026-09-13)

- Lane: sk-stable-rank-a.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).
- Analysis: `research/artifacts/sk-stable-rank-a-shortcut-2026-09-13-part1.md`.

## (a) Proposed change
None from this lane.

The brief asked whether the stable rank of `R_X = LC(X,F_2) ⋊ Z` is small enough for a sandwich theorem to replace
l.154-227. The two applicable theorems are:
- Vaserstein, LNM 854, Theorem 4, which needs `sr(R_X) ≤ 2` at `n = 3`;
- Preusser, arXiv:1912.11386, Theorem 3, which needs `R_X` to be an exchange ring.

Neither ring fact is in the literature I found, and neither is proved here. The partial results so far use the same
Kakutani–Rokhlin towers as the note:
- the odometer calibration;
- the tower idempotent for `u + u^2`;
- idempotents in one-sided ideals.

A proof of either fact would therefore be longer than the text it replaces.

The citation shortcut that does work is sk-stable-rank-b's Stepanov route
(`research/artifacts/sk-stable-rank-b-proposal-2026-09-13.md`, items A-D). It needs no stable rank and no exchange
property. On reader merits this lane recommends that route over any stable-rank version.

## (b) Independent check of the dimension count in sk-stable-rank-b's replacement text A
Take `p, q ∈ R` with exponents in `[−w, w]`, `h = 2w+1`, and `r_ρ = Σ_{0≤j<h} ρ_j u^j e_U`.
- Since `f u^m = u^m (f∘T^m)`, `p r_ρ = Σ_{i,j} ρ_j u^{i+j} (p_i∘T^{i+j}) e_U`, with `i + j ∈ [−w, 3w]`.
- If every `p_i∘T^m` and `q_i∘T^m` with `|m| ≤ 3w` is constant on `U`, the products take the form `Σ_m (Pρ)_m u^m e_U`
  over `4w+1 = h + 2w` exponents.
- There are `2h = 4w+2` unknowns, so `Pρ + Qσ = 0` has a nonzero solution.
- The elements `u^j e_U` are linearly independent for nonempty `U`, so `(r, s) ≠ 0` and `pr + qs = 0`.
- `α = (0, r, s)^T` gives `α_1 = (aα)_1 = 0`.

The count is correct.

One point for sk-referee-1 when checking the import. For a simple ring, Stepanov's Theorem 4.4 imposes conditions only
at the proper ideal `I = 0`. Check that its proof of the sandwich at level `I = R` does not use normality of
`E(3,R)` in `GL(3,R)`, which is not known for `R_X`. The replacement text only uses subgroups of `E(3,R)` normalized
by `E(3,R)`. This is a question, not a reported error.

## (c) Length change
0 lines from this lane. sk-stable-rank-b's route changes about −54 lines.

## (d) Reader-facing trade-off
The stable-rank or exchange version would be shorter only through a ring fact the reader cannot look up. That leaves a
choice between two proofs:
- the Stepanov version: shorter, but it asks the reader to trust Stepanov's 1997 theorem (J. Math. Sci. 95, 2146-2155);
- the note's version: a self-contained argument of about 73 lines using only the simplicity of `GL_d(F_2)`.

That choice is for the user.

## (e) Status
- Landed 4020f0bd04:
  - `preusser-exchange-rings-have-standard-normal-subgroups` (+ `-citation`): established import, verbatim;
  - `standard-normal-structure-makes-simple-ring-el-simple` (+ `-proof`): established, unreviewed, queued with sk-referee-1;
  - `minimal-cantor-crossed-product-has-stable-rank-at-most-two`: OPEN, with Attempts;
  - `minimal-cantor-crossed-product-is-an-exchange-ring`: OPEN, with Attempts.
- This landing:
  - route `subshift-bass-stable-rank-from-minimal-cantor-case` into sk-stable-rank-b's
    `subshift-crossed-product-ring-has-bass-stable-rank-at-most-two` (its special case);
  - `distinct_from` links to the Stepanov nodes.
