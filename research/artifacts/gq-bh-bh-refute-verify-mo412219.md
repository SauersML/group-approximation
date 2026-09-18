# Adversarial check: `fp-decidable-group-whose-e-is-not-recursively-presented` (MathOverflow 412219) (bh-refute, 2026-09-18)

Rotation item (high priority, 1c6cfe928). The coordinator asked for three focus points:
- the Clapham input at source;
- solvable WP of the amalgam;
- the co-r.e.-but-not-r.e. step.

Verdict: **PASS**. No gap was found.

## 0. The question and the reformulation

- **The reformulation.** `G * ⟨x⟩ → G^G`, `g ↦ c_g`, `x ↦ id`, has image `E(G)` and kernel `J_1(G)`. So
  `E(G) ≅ (G*Z)/J_1(G)`.
- **Recursive presentability.** For finitely presented `G`, the kernel of `F(X ∪ {x}) → G*Z` is r.e. So `E(G)`
  is recursively presented iff `J_1(G)` is r.e. as a set of words.
- **Checked:** this matches MO 412219's question as quoted on the question node, including its definition of
  `E(G)`.

## 1. Clapham at source

The primary paper (Proc. LMS (3) 17 (1967) 419–430) was not re-read. The statement was read verbatim in two
independent sources:
- **BBMZ, arXiv:2309.06224, TeX l.145:** "every finitely generated group with solvable word problem embeds in a
  finitely presented group with solvable word problem \cite{clapham}". Their bibitem is `[Cla67]`,
  C. R. J. Clapham, *An embedding theorem for finitely generated groups*.
- **FFWZ, arXiv:2603.24687, text l.1318–1321:** "the fact, due to Clapham [Cla67], that every group with solvable
  word problem embeds in a finitely presented group with solvable word problem".

This exactly matches the use in step 1. `H_0` is finitely generated (by `a, b, c`) with solvable WP.

## 2. The three lemmas, re-derived

- **Lemma 1.**
  - (⇐) `Core_K(A)` is normal in `K`, and `b` centralizes it, so it is normal in `G`.
  - (⇒) `(k^{-1}ck) b (k^{-1}ck)^{-1} b^{-1}` is a reduced alternating word of length 4 (with `b ∉ A`, since
    `⟨b⟩ ≅ Z`), hence nontrivial.
  - **Correct.**
- **Lemma 2.**
  - Generation of the fibre product: `(u,v) = (u,u)(1,u^{-1}v)`, with conjugates of `(1,r)` by `(g,g)`.
  - `k(1,W)k^{-1} = (1, h ψ^n(W) h^{-1})` for `k = (g,h)s^n`, so `(1,W) ∈ Core` iff `p(ψ^n W) = 1` for all `n`.
  - **Correct.** No finite presentability of `M` is needed.
- **Lemma 3.**
  - `T` is recursive, and every nonzero `j` is uniquely `2^e(2n+1)` with `n ∈ Z`.
  - `C` is a free factor of `⟨⟨b⟩⟩ = F(b_j)`, so membership is decidable, and `j ∉ T` gives `b_j ∉ C`.
  - `w_e(a^n) = [c, a^{2^{e+1}n} b_{2^e} a^{-2^{e+1}n}] = [c, b_{2^e(2n+1)}]`.
  - **Correct.**

## 3. Construction and solvable WP of the amalgam

- **The substitution.** `ψ: z ↦ zα` fixing `X` is a Nielsen automorphism, and `ψ^n(z) = zα^n` for `n ∈ Z`.
  Since `ψ^n` fixes `α, β, γ`, `p(ψ^n W_e) = w_e(a^n)`, computed in `H ⊇ H_0`.
- **Finite presentation of `G`.** `G = K *_M (M × ⟨b'⟩)` is the HNN extension of `K` with stable letter `b'`
  centralizing `M`. Its presentation is `K`'s relators plus `[b', m_i]` for the finitely many generators of `M`.
  So `G` is finitely presented even though `M` need not be. Checked.
- **Solvable WP.**
  - `K = (F×F) ⋊ Z` has solvable WP.
  - `(g,h)s^n ∈ M` iff `n = 0` and `p(g) = p(h)`, which is decidable because `H` (Clapham) has solvable WP.
  - Britton's lemma then decides `G`. **Correct.**

## 4. Co-r.e. but not r.e.

- **Co-r.e.** `w ∉ J_1` iff some `g ∈ G` has `w(g) ≠ 1`. Search over `g`, deciding each case by the solvable WP
  of `G * ⟨x⟩`.
- **Not r.e.** `e ↦ Ω_e` is computable, and `Ω_e ∈ J_1(G)` iff `φ_e(e)` never halts. That set is co-r.e. and
  not r.e. So `J_1(G)` is not r.e., and `E(G)` is not recursively presented.
- By Higman, the finitely generated group `E(G)` embeds in no finitely presented group. **Correct.**
- **Π_2 variant.** With `T'` r.e. and Higman in place of Clapham, `Ω_e ∈ J_1` iff `φ_e` is total. This is
  `Π_2`-complete, which matches the general `Π_2` upper bound for finitely presented `G`. It is correctly *not*
  claimed to have solvable WP.

## Attacks tried (all failed)

- **`M` is not finitely presented, so perhaps the amalgam is not either.** This is harmless; see the HNN
  presentation above.
- **The mixed identity only quantifies over `K`.** Lemma 1's (⇐) handles all of `G`, via normality in `G`.
- **Negative `n` in `ψ^n`.** `ψ^{-1}(z) = zα^{-1}`, so both signs are covered, and `T` uses `|n|`.
