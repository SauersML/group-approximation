# Referee report (gq-referee-a, proof-gap lens): char-0 representable rings in finitely presented simple rings

**Reviewed:** `char-zero-representable-rings-embed-in-fp-simple-rings` and its route `-proof` (lane gq-ring-fp-simple,
36d65161f), read on origin/main.

**Verdict: PASS.** No gaps found. Two wording fixes are needed.

- **§1, matrix rings.**
  - The presentation described (generators `g` of `R`, matrix units `e_ij`, `R`'s relators, the matrix-unit
    relations, and `[g, e_ij] = 0`) presents `R ⊗_Z M_e(Z) = M_e(R)` with `g ↦ g·I`. The coproduct modulo
    commutation is the tensor product.
  - **Wording fix:** "placed in the (1,1) corner" contradicts the commutation relations. The generators sit as
    scalar matrices `g·I`.
  - Ideals of `M_e(R)` are `M_e(I)`, so simplicity passes to `M_e(R)`.
- **§2, the embedding lemma.** Correct.
  - Lasker–Noether gives `C ↪ ∏ Q[y]/q_j`.
  - For each primary piece `A`, Noether normalization gives an injective finite map `A_0 = Q[t_1..t_k] → A`.
  - A nonzero `a ∈ A_0` is not nilpotent in `A`. In a primary ring every zero divisor is nilpotent, so `a` is
    a non-zero-divisor. Hence `A ↪ A ⊗_{A_0} F_k`, which is finite-dimensional.
  - The regular representation is unital and injective, and block diagonals over `F_{max k_j}` handle the
    product.
  - **Minor:** when every `k_j = 0` (Artinian pieces, e.g. number fields), use `Q ⊆ F_1`. The ring `R_k` is
    defined only for `k ≥ 1`.
- **§3.**
  - Tensoring over the field `Q` is flat, so `C ⊗_Q Q<x> ⊆ M_e(F_k) ⊗_Q Q<x> = M_e(F_k<x>)`.
  - Part 3 of the `R_k` node gives a unital embedding `F_k<x> ⊆ R_k` with `F_k` central. So any subring lies in
    `M_{De}(R_k)`.
- **Special cases.** All correct.
  - (1) `A ↪ A ⊗ Q`.
  - (2) A finitely generated field of characteristic 0 is finite over a purely transcendental `F_k`; use its
    regular representation.
  - (3) The entries of finitely many generators generate a finitely generated subfield.
  - (4) is immediate.
- **Group consequence.** `GL_n(E) ≤ GL_{ne}(F_k) ≤ M_{ne}(R_k)^x`. Correct.
- **Not checked.** The remark about "one uniform recursive word-problem bound" is a remark, not proved here.
