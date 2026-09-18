# Referee report (citation/hypothesis lens): `q-algebra-elementary-quotients-contain-gl-n-q`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim and its `-proof` as landed at 6c91db64f.

## Verdict

**PASS.** No amendments. The node cites nothing beyond `SL_N(Q) = E_N(Q)` over a field, which is classical row
reduction.

## Checks

1. **`Q ⊆ Z(R)`.** Inverses of central units are central. **Correct.**
2. **Centralizer.**
   - The entries of `gE_ij = E_ij g` give three facts: `g_ki = 0` for `k ≠ i`, `g_jl = 0` for `l ≠ j`, and
     `g_ii = g_jj`. So `g = dI`.
   - `r E_ij` gives `dr = rd`.
   - Two-sided invertibility of `g` gives `d ∈ Z(R)^×`.
   - **Correct.** `N >= 2` is needed, and it is assumed.
3. **Embedding of `PSL_N(Q)`.**
   - `Q → R` is injective because `R ≠ 0` and `Q` is a field.
   - `ι(g) ∈ Z(E_N(R))` forces `ι(g) = dI`, so `g` is scalar.
   - Conversely, rational scalars in `SL_N(Q)` are central in `E_N(R)`. So the kernel is exactly `Z(SL_N(Q))`.
   - **Correct.**
4. **Embedding of `GL_n(Q)`.** `β(g) = diag(g, det g^{-1}, I_{N−n−1})`. If `β(g)` is scalar, the last diagonal entry
   forces `λ = 1`, which uses `N >= n+2`. **Correct.**
5. **Matrix rings.**
   - `e_IJ(A) = ∏ e_{(I,a),(J,b)}(A_ab)`: the factors multiply to zero pairwise when `I ≠ J`, so the product is
     `I + ΣA_ab E`.
   - Within-block elementary matrices are commutators through a second block.
   - A unital ring isomorphism `R ≅ M_2(R)` carries `E_N(R)` onto `E_{2N}(R)`, and centres onto centres.
   - **Correct.**

## Downstream use checked

In `tracial-harmonic-ring-keeps-rational-scalars`, part 5 uses part 2 with `Z(R_h) = Q`. That gives
`Z(E_N(R_h)) = {λI : λ ∈ Q^×, λI ∈ E_N(R_h)} ⊆ {±I}`, using that node's part 4. The use is consistent.
