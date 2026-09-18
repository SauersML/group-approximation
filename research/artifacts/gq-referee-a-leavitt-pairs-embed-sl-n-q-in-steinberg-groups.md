# Referee report (gq-referee-a, proof-gap lens): Leavitt pairs embed SL_N(Q) in Steinberg groups

**Reviewed.**
- `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (lane gq-steinberg-q, b9dd69f0a): the proof in
  `## Attempts`, item 1, steps (a)–(f).
- Its consumer, the route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`.

**Verdict: PASS for the lemma.** The kernel of `St_N(Q) → St_(6N+1)(S)`, `x_ij(q) ↦ x_(N+i),(N+j)(q)`,
is exactly `K_2(N,Q)`. This holds for every unital ring `S ⊇ Q` with a binary Leavitt pair and every
`N ≥ 3`. So `SL_N(Q) ≤ St_(6N+1)(S)` and `GL_n(Q) ≤ St_(6n+7)(S)`. I found no gap. The
coordinator's three points are §§1, 2 and 5.

## 1. Room lemma (a), for noncommutative `S`

- **The column group is abelian.** Fix `b ∉ [k]`. For `c ≠ c'`, (R3) applies to `x_cb`, `x_c'b`,
  because `b ≠ c'` and `c ≠ b`.
- **The column action.** Conjugation by `x_ij(s)`, `i, j ∈ [k]`, fixes `x_cb(v)` for `c ≠ j` (R3) and
  sends `x_jb(v)` to `x_ib(sv) x_jb(v)` (R2). So the column vector `v` becomes `(I + sE_ij)v`, with
  `s` on the left, as matrix multiplication requires.
  - Conjugation is a homomorphism `St_k → Aut(U_b)`. It agrees with left multiplication by
    `π_k(y)` on generators, so it agrees everywhere.
- **The row action.** `x_ij(s) x_bi(v) x_ij(s)^{-1} = x_bi(v) x_bj(−vs)`. I derived this from
  `[x_bi(v), x_ij(s)] = x_bj(vs)` and the fact that `x_bj` and `x_bi` commute. So `v ↦ v(I+sE_ij)^{-1}`,
  and `y` acts by `v ↦ v π_k(y)^{-1}`.
- **Conclusion.** The remaining generators `x_bb'` commute with `ŝ(St_k)` by (R3), and for
  `c, d ∈ [k]` we have `x_cd(r) = [x_cb(r), x_bd(1)]`. So `ŝ(K_2(k,S))` is central in
  `St_{k'}(S)`. Correct.

## 2. The doubling map and block expansion (b)

- **`ψ` is a unital ring homomorphism.** `ψ(r) = (y_s r x_t)` satisfies `ψ(1) = (y_s x_t) = I`, and
  `Σ_t y_s r x_t y_t r' x_u = y_s r r' x_u`.
- **`β` respects (R1) and (R3).** The factors `x_(i,s),(j,t)` of one `β(x_ij(a))` pairwise commute
  by (R3), since `(j,t) ≠ (i,s')` and `(i,s) ≠ (j,t')`. The images of commuting generators commute
  for the same reason.
- **`β` respects (R2).** Consider `[x_(i,s),(j,t)(a_st), x_(j,t'),(l,u)(b_t'u)]`.
  - For `t = t'` it is `x_(i,s),(l,u)(a_st b_tu)`. For `t ≠ t'` it is `1`.
  - Every `x_(i,s),(l,u)` commutes with all factors on both sides (R3). So `[∏X, ∏Y] = ∏[X,Y]`.
  - By (R1) this is `∏_(s,u) x_(i,s),(l,u)((ab)_su)`, with the order of factors in `ab`
    respected.
- **The linear algebra.**
  - `𝒳𝒴 = I_N` and `𝒴𝒳 = I_2N`, since `Σ x_t y_t = 1` and `y_s x_t = δ`.
  - `π_2N ∘ Φ = 𝒴 π_N(·) 𝒳` holds on generators, and both sides are homomorphisms because
    `𝒳𝒴 = I`.
  - `Q` is central: integers are central, and inverses of central units are central. So
    `ψ(q) = qI_2`.
  - `y ↦ ŝ(y)ŝ_τ(y)` is a homomorphism, since the two images commute by (R3). Hence
    `Φ ∘ ι = ι(ŝ · ŝ_τ)` on `St_N(Q)`.

## 3. The square swap (c)

- **`W` is invertible.** `W = [[𝒴,0],[0,𝒳]]`, with row blocks `(2N, N)` and column blocks
  `(N, 2N)`. Both products with `[[𝒳,0],[0,𝒴]]` are the identity.
- **The conjugation.** `W diag(A, I_2N) W^{-1} = diag(𝒴A𝒳, 𝒳𝒴) = diag(𝒴A𝒳, I_N)`.
- **Whitehead.** The identity `diag(W, W^{-1}) = u(W) l(−W^{-1}) u(W) u(−I) l(I) u(−I)` checked
  directly: the first three factors give `[[0,W],[−W^{-1},0]]`, and the last three give
  `[[0,−I],[I,0]]`. So `D ∈ E_6N(S)` and `D diag(A, I_5N) D^{-1} = diag(𝒴A𝒳, I_4N)`.

## 4. Two lifts agree (d)

- **`e(y)` lies in `K_2`.** `π_M(e(y)) = diag(𝒴π(y)𝒳, I_4N) · diag(𝒴π(y)𝒳, I_4N)^{-1} = I`. So
  `e(y) ∈ K_2(M,S)`, and `c(y) = ŝ(e(y))` is central in `St_{M+1}(S)` by (a).
- **`c` is a homomorphism.** `c(yy') = f_1(y) c(y') f_2(y)^{-1} = c(y') c(y)`, so `c` maps into the
  centre.
- **`c` is trivial.** `St_N(S)` is perfect for `N ≥ 3`. Hence `f_1 = f_2`.

## 5. The swindle (e), and the step `z = z·z' ⇒ z' = 1`

- `ιz ∈ K_2(N,S)`, so `ŝ(ιz)` is central in `St_{m'}(S)` and `f_1(ιz) = ŝ(ιz)`.
- `f_2(ιz) = ŝ(ιŝ(z)) · ŝ(ιŝ_τ(z)) = ŝ(ιz) · ŝ_τ(ιz)`. Composites of index maps are index maps:
  initial after initial is initial, and initial after `τ` is `τ`.
- `f_1 = f_2` gives `ŝ(ιz) = ŝ(ιz) ŝ_τ(ιz)`, so `ŝ_τ(ιz) = 1`, by cancellation in a group.

## 6. Conclusion (f)

- **The kernel is exactly `K_2(N,Q)`.** It contains `K_2(N,Q)` by (e). Conversely, the image in
  `GL_{m'}(S)` is `π_N(y)` in the block `N+1..2N`, and `M_N(Q) → M_N(S)` is injective.
- **The image.** `E_N(Q) = SL_N(Q)`, so the image is `SL_N(Q)`.
- **`GL_n(Q)`.** `g ↦ diag(g, det g^{-1})` embeds `GL_n(Q)` in `SL_(n+1)(Q)`, and `N = n+1 ≥ 3`.

## 7. The route to Problem 2.7 (`gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`)

- **Inputs.** Given the lemma and `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, whose
  proof-gap review I passed at 8f4edc918, the route needs only three things: `Q ⊆ R_L`, the Leavitt
  pair `(s_i, t_i)`, and finite presentation of `R_L`. It does not need simplicity.
- **Finite presentation and (T).** Finite presentation of `St_m(R_L)` for `m ≥ 4` is Krstić–McCool,
  Theorem 3. Property (T) is Ershov–Jaikin-Zapirain, arXiv:0809.4095v2, Theorem 6.2. Both are
  imported in `steinberg-finite-presentation-and-kazhdan-theorem`, but the Krstić–McCool primary
  text was not read there. That is the citation referee's lens.
- **Result.** If those hold, `St_(6n+7)(R_L)` is a finitely presented group with property (T),
  given as the Steinberg group of an explicit 6-generator, 9-relation ring, and it contains
  `GL_n(Q)`.
- **Two notes for the claim "explicit and natural".**
  1. Problem 2.7 asks for an explicit example. Writing out the finite presentation of
     `St_(6n+7)(R_L)` that the Krstić–McCool theorem supplies (generators `x_ij(g)`, `g` a ring
     generator, with finitely many relators) would make "explicit" literal. At present the route
     says the presentation "is not written out".
  2. "Natural" is a judgement for the authors of the problem. Don't state it as a theorem.
- **Priority** was not checked (for `gq-lit-arxiv`).

## 8. Non-blocking remarks

- The "optional sharpening" (Attempt 2) is correctly marked as unneeded.
- The argument is an unstable Eilenberg swindle. It is in the spirit of the stable vanishing of
  Leavitt `K`-theory, but it is self-contained and gives the explicit rank `6N+1`.
