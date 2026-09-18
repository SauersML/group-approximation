# Referee report (gq-referee-a, proof-gap lens): isometric frames over rank-one bases fail the K-budget

**Reviewed:** `isometric-frames-over-rank-one-bases-fail-the-k-budget` and its `-proof` (lane gq-infinite-primes,
74de4d286), read on origin/main.

**Verdict: PASS.** Items 1–4 hold, and I found no gap. There are three nits. N1 fixes a wording mismatch between (R1)
and the proof's setting check. Bass/Vaserstein cancellation, Quillen's filtered-ring theorem and Stafford are for the
citation lens.

## The five points the author asked about
- **The exact rescaling `m[p] = n[1]` in the torsion case.**
  - `[p]⊗1 = r[1_B]⊗1` with `r = n/m` in lowest terms, so `m[p] − n[1_B]` is torsion, of some order `e`. Then
    `(em)[p] = (en)[1_B]` exactly.
  - `em ≠ en` if and only if `r ≠ 1`, so item 1 is unaffected.
  - For `r = 1` the relation `(em)[p] = (em)[1_B]` is what item 2 uses. ✓
  - The statement of (R1), however, says "`m[p] = n[1_B]` for unique coprime integers". Exact equality may need the
    non-coprime pair `(em, en)` (N1).
- **The choice `x = P_j x` and `y = y P_j`.** It is automatic: from `xy = P_j` and `yx = 1_j`, we get
  `P_j x = x(yx) = x` and `y P_j = (yx)y = y`.
  - `x` and `y` exist because `P_j B^(jk) = (pB^k)^j ≅ B^j`. Take the inclusion composed with the isomorphism, and
    the inverse composed with the projection.
  - Then `UV = S P_j T = (ST)² = 1_j` and `VU = y P_j x = yx = 1_j`. ✓
- **`ker(Q^× → K_1(M_j R)) = {λ : λ^j ∈ K}` and its finite generation.**
  - Under Morita, `λ1_j ∈ GL_1(M_j(R)) = GL_j(R)` is `diag(λ,…,λ)`, of class `j[λ] = [λ^j]`. So the kernel is
    `K' = {λ : λ^j ∈ K}`.
  - If `K'` is finitely generated, so is its subgroup `K`.
  - Conversely, if `K` is finitely generated, it involves finitely many primes. Every `λ ∈ K'` has prime support
    inside that finite set, so `K' ⊆ {±1} × Z^(S')` is finitely generated. ✓
- **`E_N(M_j(R)) = E_(jN)(R)` for `N ≥ 2`.**
  - `⊆`: the block elementary matrix `e_(ab)(A)`, `a ≠ b`, is the product of the commuting `e_((a,u),(b,w))(A_(uw))`.
    Their products `E_((a,u),(b,w))E_((a,u'),(b,w'))` vanish because `a ≠ b`.
  - `⊇`: an elementary `e_((a,u),(c,v))(r)` with `a ≠ c` is block elementary. For `a = c` (`u ≠ v`), take
    `[e_((a,u),(b,w))(r), e_((b,w),(a,v))(1)] = e_((a,u),(a,v))(r)` for some block `b ≠ a`, which exists since
    `N ≥ 2`. The indices are distinct, so the matrix identity `[I + rE_ij, I + E_jk] = I + rE_ik` applies. ✓
- **Homogeneity of the frame relations in item 4.** Put `B` in degree 0, `s_i` in degree 1 and `t_i` in degree −1 in
  `B * Z⟨s,t⟩`. Then:
  - `t_is_j − p_ij` has degree 0;
  - `b s_i − Σ_l s_l(t_l b s_i)` has degree 1;
  - `t_i b − Σ_l (t_i b s_l)t_l` has degree −1;
  - `st − 1`, the relations `t_l b s_i = φ(b)_(li)` and the relations of `B` all have degree 0.

  The ideal is homogeneous, so the quotient is graded. ✓

## Other checks
- **Item 2.** `[(pB^k)^m] = [B^m]` means that `(pB^k)^m ⊕ B^a ≅ B^(m+a)` for some `a`. Taking `d` copies makes the rank
  `md ≥ d`, and cancellation gives `(pB^k)^(md) ≅ B^(md)`. ✓
- **Item 3, the grading.** `U = Sx` has entries in `R_1·R_0 ⊆ R_1`, and `M_j(R)_n = M_j(R_n)` is a ring grading.
  `Q ⊆ M_j(R)` as scalars, unitally. So the graded node applies to `M_j(R)`, and the two translations above carry it
  back to `R`. ✓
- **`R_L`.** A localization of the PID `Q[N]` is a PID. So `K_0 = Z`, `[1]` has infinite order and `sr ≤ 2`. The index
  is `r = 2`. ✓

## Nits
- **N1 ((R1) versus the setting check).** Replace "`m[p] = n[1_B]` for unique coprime integers `m ≥ 1`, `n ≥ 0`" with
  "the ratio `r = n/m` is unique; choose `m ≥ 1` and `n` with `m[p] = n[1_B]` exactly (possibly not coprime)".
  - Also, the sign `n ≥ 0` is not forced by (R1) for rings without a state. It is used nowhere.
- **N2 ((BC)).** State the normalization of stable range, Vaserstein's, with `sr(field) = 1`. Under it, `P ⊕ B ≅ B^(n+1)`
  with `n ≥ sr(B)` gives `P ≅ B^n`. Bass's `SR_n` is shifted by one.
- **N3 (item 3).** Replace "we may take `x = P_j x`, `y = y P_j`" with the one-line derivation above, since the
  equalities are automatic.
