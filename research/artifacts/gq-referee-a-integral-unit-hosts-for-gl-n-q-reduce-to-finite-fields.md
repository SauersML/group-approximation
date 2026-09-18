# Referee report (gq-referee-a, proof-gap lens): integral unit hosts reduce to finite fields

**Reviewed:** `integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields` with its route `-proof`
(lane gq-ring-leavitt, 7af878fd4), read on origin/main.

**Verdict: PASS.** One sentence should be added (§2). Part 4's `K_1` input is the citation lens.

## 1. Parts 0–1 (residually finite-field)
- **Part 0.** Correct. The structure constants are integral, so `A_D` is a subring. `A_D ≅ D^(B)`, so
  `A_D → A_K` is injective.
- **Part 1.** Correct.
  - `S ≤ GL_m(A_D)`, because `D` contains the coordinates of both the `g_i` and the `g_i^{-1}`.
  - A finitely generated domain over `Z` or `F_p` is Jacobson with radical `0`, and its residue fields
    are finite.
  - `∩ ker ρ_m = (∩ m)^(B) = 0`.

## 2. Part 2 (transfer of `SL_n(Q)` and `PSL_n(Q)`)
- **Setup.** Correct in both cases. In (b), `Z_P = P ∩ K^x·1` is central because `K` is central in
  `A_K`.
- **Perfectness of `P'` in case (b): add one sentence.** The proof says "since `P'` is perfect". That
  is true, but it needs the standard argument: `π(P) = P_0` is perfect and `Z_P` is central, so
  `P = P' Z_P` and `[P,P] = [P'Z_P, P'Z_P] = [P',P']`. In case (a), `P' = P` directly.
- **Some reduction has central kernel.** Correct. If `π(N_m) = P_0` for every `m`, then
  `P'/N_m ≅ (P'∩Z_P)/(N_m∩Z_P)` is abelian and perfect, hence trivial. So `P' = ∩ N_m = 1`, which is
  a contradiction.
- **Case (a).** `N_m ≤ Z_P ≤ {±I}`, so `G_F ≅ SL_n(Q)` or `PSL_n(Q)`. Correct.
- **Case (b).** `1 ∈ B` forces scalars `λ·1 ∈ A_D` to have `λ ∈ D`, and the same holds for `λ^{-1}`.
  So `ρ_m(Z_P) ≤ F^x·1`, and `C = G_F ∩ F^x·1` maps to the centre of `P_0`. Hence `C = C_0`, and
  `G_F F^x/F^x ≅ PSL_n(Q)`. Correct.
- **Lifting `(Q,+)`.** Correct.
  - The commutator pairing factors through `Λ²_Z Q = 0`, so `Ẽ` is abelian.
  - `Ext^1(Q, C_0) = 0`, because `|C_0|` is invertible on `Q` and kills `C_0`.
  - So `Ẽ ≅ Q ⊕ C_0`.

## 3. Part 3 (`(Q,+)` and `F[Q]`)
- **The two directions.** Correct. A unit of infinite order over a finite field is transcendental, so
  the `F[x_k^{±1}]` are Laurent rings and the union embeds.
- **The embedding into `M_(∞!)(F) ⊗ F[t^{±1}]`.** Correct.
  - The exponents `((k+1)j + i)/(k+1)!` enumerate `0..(k+1)!−1` once.
  - With `i` outer, multiplication by an element of level `k` is `diag(a, …, a)`.
- **The sufficient condition.** Correct.
  - Kernels of maps out of `M_{k!}(F[u^{±1}])` are `M_{k!}(I)`.
  - For `f ∈ I`, `f(u) = Σ E_{i1} f(u) E_{1i} = 0`, and `u` is transcendental, so `f = 0`.
- **Infinite rank.** Correct. `F(u)` is flat over `F[u]`, and `F[Q]` is free over `F[t^{±1}]` on
  `{t^q : 0 ≤ q < 1}`.

## 4. Part 4 (not a corner)
- **Corners have finite `K_1`.** `K_1(L_F(1,d)) = F^x/(F^x)^{d−1} ⊕ 0`, which is finite. Nonzero
  corners of the simple ring `M_m(L_F(1,d))` are full, and `K_1` is Morita invariant for full corners.
- **`F[Q]` has infinite `K_1`.** `det` gives a split surjection `K_1(F[Q]) → F[Q]^x ⊇ Q`.
- Correct. The Ara–Brustenga–Cortiñas exact sequence is cited, which is the citation lens.

## 5. Consequences
- **The reductions stated for Leavitt hosts and for `Λ = L_Q(1,2)^x/Q^x` follow.** For `L_Z(1,2)`,
  `1` is the empty normal-form word, so `Z·1` is a direct summand. A finitely generated `D ⊆ Q` is some
  `Z[1/N]`, so its residue fields are prime fields.
- **The "one conjecture closes the route" bullet is correctly conditional.**
- **This does not touch the Steinberg route for Problem 2.7.** `R_L`, `R_Q` and `D` contain `Q` in
  their ring, so their additive groups are not free abelian. They lie outside part 1, as the node's
  last bullet says.
