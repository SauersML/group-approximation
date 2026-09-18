# Referee report (citation/hypothesis lens): `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` and `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: both nodes as landed at 020c46bf5 and 6431e0989. gq-referee-a
had already passed the first on the proof-gap lens.

## Verdict

- **`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`: PASS.**
  - It cites nothing beyond `SL_m(Z) = E_m(Z)`, which is classical, and the parent lemma, which I passed in
    `gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`.
  - I checked the new computations below.
- **`st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`: PASS**, with one scope remark (R1).

## The St_{3N+1} node

**Change 1 (`W` is elementary).** Block products, with row and column blocks as stated:
- `U_1 W = [[𝒴,0],[𝒳𝒴, 𝒳]] = [[𝒴,0],[I_N,𝒳]]`.
- `U_2 U_1 W = [[𝒴−𝒴, −𝒴𝒳],[I_N,𝒳]] = [[0,−I_2N],[I_N,𝒳]]`.
- Right multiplication by `U_3` gives `[[0,−I_2N],[I_N, −𝒳+𝒳]] = P`.
- The permutation of `P` is `j ↦ j+2N` for `j <= N` and `j ↦ j−N` otherwise, that is `i ↦ i+2N mod 3N`. It is
  a product of `N` three-cycles, so it is even, and `P` has `2N` minus signs. So `det P = 1`.
- `P ∈ SL_3N(Z) = E_3N(Z)`, since `Z` is Euclidean. Hence `W ∈ E_3N(S)`.
- Step (d) with `D = W`: `W diag(A, I_2N) W^{-1} = diag(𝒴A𝒳, I_N)`, so `π_{3N}(e(y)) = I`. The room lemma applies
  at `m' = 3N+1 > 3N`.

**Change 2 (coefficients in the centralizer `A`).**
- `ψ(a) = (y_s a x_t) = a·(y_s x_t) = aI_2`, because `a` commutes with the pair.
- Nothing else in (b)–(f) uses centrality in `S`.
- The kernel lies in `K_2(N,A)` because `A → S` is injective. The image is `E_N(A)`.

**Part 2.**
- `R_2C_2 = 1` and `C_2R_2 = I_2`.
- The recursions give `R_{k+1}C_{k+1} = R_k diag(I, R_2C_2) C_k = 1` and
  `C_{k+1}R_{k+1} = diag(I, C_2R_2) = I_{k+1}`.
- So `θ_k` is a unital ring isomorphism, and `St_10(M_k(S)) ≅ St_10(S)`.
- The scalar matrices `x_sI_k`, `y_sI_k` form a Leavitt pair in `M_k(S)`, and `M_k(Q)` centralizes them because
  `Q` is central.
- `E_3(M_k(Q)) = SL_3k(Q)`:
  - it contains every between-block elementary matrix;
  - within-block ones are commutators through the third block;
  - so it contains `E_3k(Q) = SL_3k(Q)`, and it has determinant 1.
- Hence `GL_n(Q) ≤ St_10(S)` for every `n`. For finitely presented `S`, for example `R_L`, this is one finitely
  presented group, by Krstić–McCool at rank 10 >= 4.

## The ring-quotient relator node

- **Step 1.** `x_ij(r̄) ↦ x_ij(r)K` is well defined, since `x_ij(r) = x_ij(r')x_ij(r−r')`. It respects (R1)–(R3)
  and inverts the natural surjection. Correct.
- **Step 2.** Each listed commutator identity is an instance of (R2) with distinct indices. Together they cover
  every pair `(k,l)`, `k ≠ l`, starting from `x_12(ρ)`. Correct.
- **Step 3.** `[x_kl(ρ), x_lj(b)] = x_kj(ρb)`, then `[x_ik(a), x_kj(ρb)] = x_ij(aρb)`. Correct.
  - This works already for `n >= 3`: take `l = i`, so that `[x_ki(ρ), x_ij(b)] = x_kj(ρb)`.
  - The stated `n >= 4` is harmless.
- **Generation of `St_n(Z⟨g⟩)`** by `x_ij(1)` and `x_ij(g_k)`, through iterated commutators and (R1). Correct.

**R1 (scope remark).** The resulting presentation of `St_n(F/I)` is explicit only relative to an explicit finite
presentation `⟨X | Rel⟩` of `St_n(Z⟨g_1..g_d⟩)`.
- Krstić–McCool Theorem 3 gives finite presentability. Their primary text was not read, by this lane or by
  `gq-steinberg-q-krstic-mccool-source.md`.
- It is not verified whether their proof writes `Rel` out explicitly.
- Until someone reads it, say "finitely many relators added to Krstić–McCool's presentation", not "an explicit
  presentation of `St_10(R_L)`".
