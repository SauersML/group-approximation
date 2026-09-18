# Referee report (gq-referee-b, citation/hypothesis lens): T_p Attempt 4 on the central-deformation Euler host

**Reviewed.** The item "(C2, skew-Laurent level) The Euler symbols are invisible from `T_p`" of
`central-deformation-euler-host-has-fng-steinberg-residual` (OPEN; lane gq-k2-q), read on origin/main (db7acc3f9).

**Verdict: PASS.** Both inputs apply within their hypotheses, and the argument is correct. Its closing
"Not covered" list is accurate.

## Input 1: Quillen homotopy invariance for D

- **The statement used.** `K_n(R[t]) ≅ K_n(R)` for `R` left noetherian and left regular, meaning every finitely
  generated left module has finite projective dimension.
  - This is Quillen, *Higher algebraic K-theory I*, LNM 341, §6: the fundamental theorem for `G`-theory, with
    `K = G` for regular rings.
  - It does not require commutativity. I did not re-read it at source; the statement is standard.
- **`D` meets the hypotheses.**
  - `A = Z[u][π_k^(-1)]` is a localization of `Z[u]`, so it is commutative, noetherian, and of global dimension `≤ 2`.
  - `D = A[x^(±1); σ]`, with `σ` an automorphism. It is left and right noetherian (Hilbert basis theorem for skew
    Laurent extensions).
  - Its global dimension is `≤ gl.dim A + 1 ≤ 3`: the skew polynomial extension adds 1, and the Laurent ring is a
    localization.
  - So `D` is left regular noetherian, and `K_2(D) ≅ K_2(D[t])`. **Applies.**
- **A second, silent use.** The same theorem gives `K_i(Z[u]) = K_i(Z)`, which the finiteness step uses as
  `K_1(Z[u]) = {±1}` and `K_2(Z[u]) = K_2(Z) = Z/2`. Name this use.

## Input 2: ABC for Z[u][x^(±1); σ]

- **Hypotheses.** `abc-twisted-laurent-k-theory-fibration` (ABC Theorem 3.6 and Lemma 7.2, read at source there)
  needs:
  - `R` regular supercoherent: `Z[u]` qualifies, since all `Z[u][t_1..t_p]` are regular noetherian;
  - `σ` an automorphism: `u ↦ u + l` qualifies.
- **The resulting sequence.** `K_2(Z[u]) →(1−σ) K_2(Z[u]) → K_2(Z[u][x^(±1);σ]) → K_1(Z[u]) →(1−σ) K_1(Z[u])`.
  - `σ` acts trivially on `K_*(Z)`, so both `1−σ` maps are zero.
  - So `K_2(Z[u][x^(±1);σ])` is an extension of `{±1}` by `Z/2`, of order `≤ 4`. **Correct.**

## The argument (checked)

- **`φ` is a ring map.** `φ : B → D[t]` is defined by `u ↦ u`, `b ↦ tπ_0^(-1)`, `x ↦ x`. All four relations hold:
  `p ↦ t`, `t` is central, and `x t x^(-1) = t`.
- **The two evaluations.**
  - `ev_1 ∘ φ` is the quotient `B → B/(p−1) = D`.
  - `ev_0 ∘ φ` kills `b`, and it lands in the subring `⊕ Z[u] x^k = Z[u][x^(±1);σ]`, since `Z[u]` is `σ`-stable.
- **Homotopy.** `ev_0` and `ev_1` are left inverses of `D → D[t]`, which is a `K_2`-isomorphism. So they agree on
  `K_2(D[t])`.
- **The retraction.** `T_p → B × Z → D × Z` equals `T_p → T_l → D × Z`.
- **The intersection is zero.** An element in the image that lies in the span of the `c_q` projects to a finite-order
  element of the free group spanned by the `c_q` in `K_2(D)`. So it is `0`.
- **"Not covered".** The list is accurate: kernel classes of `K_2(T_p) → K_2(T_l)`, the unstable `K_2(N, ·)`, and
  whether those classes die in every finite quotient.
