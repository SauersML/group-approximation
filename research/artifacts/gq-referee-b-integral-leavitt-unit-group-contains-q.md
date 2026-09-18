# Referee report (citation/hypothesis lens): `integral-leavitt-unit-group-contains-q`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim and its `-proof` as landed at c71dd8fe4. gq-referee-a
passed it on the proof-gap lens.

## Verdict

**PASS.** Every step checks, and the only external inputs are standard. One citation amendment (A1).

## Checks

- **Step 1.**
  - `E_ab E_cd = δ_bc E_ad`, since `y_{g_b}x_{g_c} = δ_bc` for incomparable words.
  - `(1 − e_Γ)E_ab = 0`, so `u(Γ,M)u(Γ,M') = u(Γ,MM')`.
  - Injectivity comes from `E_1a(ΣM E)E_b1 = M_ab E_11`, with `E_11 ≠ 0` and `L` torsion-free.
- **Step 2.** `x_{g_a}y_{g_b} = Σ_j x_{g_a w_j} y_{g_b w_j}`, using `y_{uv} = y_v y_u`. This gives
  `u(Γ,M) = u(Γ*W, I_s ⊗ M)`, with the outer index `j` matching `I_s ⊗ M`.
- **Step 3.**
  - `v_g x_{e_i w} = x_{d_i w}` and `y_{e_i w} v_g^{-1} = y_{d_i w}`, both checked from `v_g^{-1} = Σ x_{e_i} y_{d_i}`.
  - Transitivity: two `r`-tuples with nonempty complements are `V`-related after splitting the complements to equal
    size.
  - `u(Γ,P) ∈ V` for a permutation matrix `P`.
- **Step 4.**
  - `a_1 = 1 + E_21 = 1 + x_{01}y_{00} = t`.
  - `(QD)^{k+1} = ∏_{i=1}^{k+1} Q^iDQ^{-i} · Q^{k+1} = I_{k+1} ⊗ T_k`, with `Q = P ⊗ I` cyclic of order `k+1`.
  - The complements are nonempty because every word starts with `0`.
- **Step 5.**
  - Well defined: `a_{k'}^{k'!/k!} = a_k` by iterating.
  - `t^m = 1 + m·x_{01}y_{00}`, since `(x_{01}y_{00})^2 = 0`, and this is not 1 because `L` is torsion-free.
  - A subgroup of `Q` meeting `Z` trivially is `0`.
- **Step 6.**
  - `u(Γ_{k+1}, D) = u(Γ^0_{k+1}, T_k)`: the identity blocks cancel against `1 − e`.
  - It is `V`-conjugate to `a_k`, and induction from `a_1 = t` gives finite generation.
- **Step 7.** `L` is free over `Z`, so `L ⊆ A ⊗ L` when `char A = 0`.
- **Consequences.**
  - `GL_r(Z) = ⟨E_r(Z), a transposition⟩` inside `⟨V,t⟩`.
  - Distortion passes to finitely generated overgroups.
  - `t` is not conjugate to `t^p`: `L` is faithful on `LC(C,Z)`, because `L ⊆ L_Q(1,2)` is simple. The image of
    `t − 1` is the direct summand `LC(01, Z)`, while `t^p − 1` has image `p·LC(01, Z)`. Conjugates have isomorphic
    cokernels.
  - **Correct.**

## Citations

- **A1.** "`L` is a free `Z`-module (Leavitt normal form)" is load-bearing in Steps 1, 5 and 7, and the node gives no
  citation. Cite a normal-form basis for Leavitt path algebras over commutative rings: M. Tomforde, *Leavitt path
  algebras with coefficients in a commutative ring*, J. Pure Appl. Algebra 215 (2011), or a Bergman diamond-lemma
  argument, as in the repo's `L_Z(1,d)` basis node. I did not read Tomforde here. Mark it "standard, not re-read".
- **Simplicity of `L_Q(1,2)`.** Needed for faithfulness. It is AGP Theorem 4.2, verified at source in
  `gq-referee-b-leavitt-scalar-commutators-block-fp-central-quotients.md`.
- **`V ≤ U(L)` by permutation units.** Standard. The proof uses only the displayed formulas, which I checked
  directly.

## Scope

- Novelty was not searched; the node says so.
- This is not a named stepping stone, since `(Q,+)` already lies in `VA`. What is new is that the copy sits in a
  finitely generated overgroup of `V` inside `U(L_Z(1,2))`.
- That overgroup contains `SL_3(Z)`, so it passes O1–O4. So it is a candidate host, with no finite presentation or
  simplicity claimed.
