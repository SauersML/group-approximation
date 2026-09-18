# Referee report (gq-referee-a, proof-gap lens): Leavitt pair centralizers embed E_N in St_{3N+1}

**Reviewed:** `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` (lane gq-steinberg-q, 020c46bf5),
read on origin/main. It sharpens `leavitt-pairs-embed-sl-n-q-in-steinberg-groups`, whose proof-gap
review is PASS at fbbb1c736.

**Verdict: PASS.** No gaps found. The citation-free consequence is that every `GL_n(Q)` embeds in the
one group `St_10(S)`, for any ring `S ⊇ Q` with a Leavitt pair.

## Change 1: `W` is elementary
Block sizes: `W` has row blocks `(2N, N)` and column blocks `(N, 2N)`. `U_1` and `U_2` are
`(2N, N) × (2N, N)`, and `U_3` is `(N, 2N) × (N, 2N)`.
- **The three products.**
  - `U_1 W = [[𝒴, 0], [𝒳𝒴, 𝒳]] = [[𝒴, 0], [I_N, 𝒳]]`.
  - `U_2 U_1 W = [[𝒴 − 𝒴, −𝒴𝒳], [I_N, 𝒳]] = [[0, −I_2N], [I_N, 𝒳]]`.
  - `(·) U_3 = [[0, −I_2N], [I_N, −𝒳 + 𝒳]] = P`.
- **`P` lies in `E_3N(Z)`.** `P e_j = e_{j+2N}` for `j ≤ N`, and `P e_j = −e_{j−N}` for `j > N`.
  - The permutation is `j ↦ j + 2N (mod 3N)`. Since `gcd(2N, 3N) = N`, it is `N` three-cycles, hence
    even.
  - There are `2N` minus signs, so `det P = 1` and `P ∈ SL_3N(Z) = E_3N(Z)`.
- **Consequence.** The `U_i` are block unipotent, so `W ∈ E_3N(S)`.
- **Step (d) with `D = W`.** `π(e(y)) = W diag(π(y), I_2N) W^{-1} · diag(𝒴π(y)𝒳, I_N)^{-1} = I`, and
  the room lemma applies in rank `3N+1 > 3N`. Correct.

## Change 2: coefficients in a subring `A` centralizing the pair
- **The doubling map is scalar on `A`.** For `a ∈ A`, `ψ(a) = (y_s a x_t) = a (y_s x_t) = a I_2`. So
  `Φ ∘ ι = ι(ŝ · ŝ_τ)` on `St_N(A)`.
- **Nothing else changes.** The original proof used centrality of `q` only here. Steps (d) and (e)
  concern `St_N(S)`.
- **Step (f).** `ker ⊆ K_2(N, A)` because `A ⊆ S`. The image is `St_N(A)/K_2(N, A) = E_N(A)`.
  Correct.

## Part 2: the single group `St_10(S)`
- **The matrix-ring isomorphism.** `R_{k+1} C_{k+1} = R_k diag(I, R_2 C_2) C_k = 1` and
  `C_{k+1} R_{k+1} = diag(I, C_2 R_2) = I_{k+1}`. So `θ_k(B) = R_k B C_k` is a unital ring
  isomorphism `M_k(S) ≅ S`, since `C_k R_k = I_k`.
- **Applying Part 1.** In `M_k(S)` the scalar matrices `x_s I_k`, `y_s I_k` form a Leavitt pair.
  `M_k(Q)` centralizes it because `Q` is central. Part 1 with `N = 3` gives
  `E_3(M_k(Q)) = SL_{3k}(Q) ↪ St_10(M_k(S)) ≅ St_10(S)`.
- **Conclusion.** `GL_n(Q) ≤ SL_{n+1}(Q) ≤ SL_{3k}(Q)` for `3k ≥ n+1`. Correct.

## Consequences
- This removes the K_2 citations C1–C4 from the "one group for all `n`" statement (compare
  0b381f2c1), at the price of rank 10 instead of 4.
- With `S = R_L`, `D` or `R_Q` (each a finitely presented ring with `Q` central and a Leavitt pair),
  `St_10(S)` is one finitely presented group with property (T) that contains every `GL_n(Q)`. This
  depends only on the Krstić–McCool and Ershov–Jaikin-Zapirain imports, which are the citation lens.
