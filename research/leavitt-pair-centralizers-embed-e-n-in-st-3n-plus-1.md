---
rg: 2
id: leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1
kind: claim
title: If a subring A centralizes a binary Leavitt pair of S, then E_N(A) embeds in St_(3N+1)(S); so St_10(S) contains every GL_n(Q) when Q ⊆ S
distinct_from:
  leavitt-pairs-embed-sl-n-q-in-steinberg-groups: that is the established case A = Q at rank 6N+1, which uses Whitehead's lemma; this factors the swap matrix itself into elementary matrices (rank 3N+1) and allows any centralizing subring A, which gives all GL_n(Q) in one group.
  one-steinberg-group-contains-every-gl-n-q: that puts every GL_n(Q) in St_4(S) through K_2 centrality for stable rank one and compatible refinements, with cited inputs; this reaches St_10(S) by the elementary swindle alone.
artifacts:
  - research/artifacts/gq-referee-a-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md
  - research/artifacts/gq-referee-b-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md
  - research/artifacts/gq-gq-lit-arxiv-priority.md
---

**ESTABLISHED (2026-09-17)** through `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1-proof`
(lane `gq-steinberg-q`; Attempt 1 below).

**Review status.**
- `gq-referee-a` PASS, on the proof-gap lens (`research/artifacts/gq-referee-a-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md`).
- `gq-referee-b` PASS, on the citation and hypothesis lens (`research/artifacts/gq-referee-b-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md`).
- Priority: `research/artifacts/gq-gq-lit-arxiv-priority.md` §7 found no finite-rank unstable Leavitt swindle and no finitely presented Steinberg-group overgroup of `GL_n(Q)`.

**Statement.** Let `S` be a unital ring with a Leavitt pair `x_1, x_2, y_1, y_2`
(`y_i x_j = δ_ij`, `x_1 y_1 + x_2 y_2 = 1`). Let `A ⊆ S` be a unital subring whose elements
commute with every `x_i` and `y_i`, let `N >= 3`, and let `τ : [N] -> [3N+1]` be `i -> N+i`.
1. The map `St_N(A) --τ--> St_(3N+1)(A) -> St_(3N+1)(S)` has kernel exactly `K_2(N,A)`. So
   `E_N(A)` embeds in `St_(3N+1)(S)`.
2. If `Q ⊆ S` is a unital subring, then `SL_(3k)(Q)` embeds in `St_10(S)` for every
   `k >= 1`. Hence every `GL_n(Q)`, `n >= 1`, embeds in the one group `St_10(S)`.

## Attempts

1. **Proof (referee PASS a, b).** This is the proof of
   `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (steps (a)–(f)) with two changes.

   **Change 1: `W` is elementary, so no Whitehead doubling.** Let `𝒴, 𝒳, W` be as in step (c)
   there. Consider the block unipotents
   - `U_1 = [[I_2N, 0], [𝒳, I_N]]`,
   - `U_2 = [[I_2N, -𝒴], [0, I_N]]`,
   - `U_3 = [[I_N, -𝒳], [0, I_2N]]`.

   Each is a product of elementary matrices. Using `𝒳𝒴 = I_N` and `𝒴𝒳 = I_2N`:
   - `U_1 W = [[𝒴, 0], [I_N, 𝒳]]`;
   - `U_2 U_1 W = [[0, -I_2N], [I_N, 𝒳]]`;
   - `U_2 U_1 W U_3 = P = [[0, -I_2N], [I_N, 0]]`.

   `P` is a signed permutation matrix over `Z`. Its permutation is `i -> i + 2N (mod 3N)`,
   a product of `N` three-cycles, so it is even. It has `2N` minus signs. So `det P = 1`,
   and `P ∈ SL_3N(Z) = E_3N(Z)`. Hence `W = U_1^(-1) U_2^(-1) P U_3^(-1) ∈ E_3N(S)`.
   Run step (d) with `D = W`, `M = 3N` and `m' = 3N+1`. The room lemma still applies,
   since `M < m'`.

   For `N = 1` the factorization reads
   `e_23(-y_2) e_13(-y_1) e_32(x_2) e_31(x_1) · W · e_12(-x_1) e_13(-x_2) = P`, with
   `W = [[y_1,0,0],[y_2,0,0],[0,x_1,x_2]]`.

   **Change 2: coefficients in A.** In step (b), `ψ(a) = (y_s a x_t) = a I_2` for `a ∈ A`,
   because `a` commutes with the pair. So `Φ(ι x_ij(a)) = x_ij(a) x_(N+i),(N+j)(a)`, and
   `Φ(ι y) = ι(ŝ(y) ŝ_τ(y))` for all `y ∈ St_N(A)`. Steps (d) and (e) never use that the
   coefficients are central. In step (f), the kernel lies in `K_2(N,A)`, because `A -> S` is
   injective, and `St_N(A)/K_2(N,A) = E_N(A)` by definition.

   **Part 2.** The Leavitt pair gives unital ring isomorphisms `θ_k : M_k(S) -> S` for
   every `k`.
   - Put `R_2 = (x_1, x_2)` and `C_2 = (y_1; y_2)`. Then
     `R_(k+1) = R_k · diag(I_(k-1), R_2)` and `C_(k+1) = diag(I_(k-1), C_2) · C_k`
     satisfy `R_k C_k = 1` and `C_k R_k = I_k`.
   - Then `θ_k(B) = R_k B C_k` is a unital ring isomorphism, with inverse `r -> C_k r R_k`.

   In `M_k(S)`, the scalar matrices `x_s I_k`, `y_s I_k` form a Leavitt pair, and `M_k(Q)`
   commutes with them because `Q` is central in `S`. Apply part 1 to `(M_k(S), M_k(Q))`
   with `N = 3`: `E_3(M_k(Q))` embeds in `St_10(M_k(S))`, which is `St_10(S)` via `θ_k`.
   Finally `E_3(M_k(Q)) = SL_(3k)(Q)`:
   - it contains every elementary matrix of `M_3k(Q)` between different blocks;
   - within-block ones are commutators through a third block;
   - and `E_3k(Q) = SL_3k(Q)`.

   So `GL_n(Q) ≤ SL_(n+1)(Q) ≤ SL_(3k)(Q) ≤ St_10(S)` for `3k >= n+1`.

   *For the referees:* the only new computation is Change 1, the elementary factorization of
   `W`, which uses no Whitehead lemma.
