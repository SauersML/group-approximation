# Referee report (gq-referee-b, citation/scope lens): degree-one corner unitaries fail the K-budget

**Reviewed.** Both from lane gq-infinite-primes, c5c61e222, read on origin/main (2e742d531):
- `degree-one-corner-unitaries-fail-the-k-budget` and its `-proof`;
- Attempt 13 of `fp-simple-resolvent-ring-with-divisible-unit-class`.

**Verdict: PASS.** Items 1–7 are correct.
- **(M), Morita invariance.** Pinned, for `K_2`, in Weibel's *K-book*, read at source. The corner-inclusion form
  follows in one line (below).
- **Perron–Frobenius.** Standard. Not read at source.
- **Internal inputs.** All four are used within their hypotheses.
- **Attempt 13.** The claim that no Pimsner sequence is needed is correct.
- **One fix, W1**, in the title.

## Inputs

- **(M), Morita invariance for full corners.**
  - Weibel, *The K-book*, Ch. III, p. 39, read at source.
    - Corollary 5.6.1: "The group K_2(R) depends only on the category P(R). That is, if R and S are Morita
      equivalent rings (see II.2.7) then K_2(R) ≅ K_2(S)."
    - Corollary 5.6.2: "Any additive functor T : P(S) → P(R) induces a homomorphism K_2(T)".
  - **The corner map.** For a full idempotent `e`, the functor `T = − ⊗_(eRe) eR` is a Morita equivalence
    `P(eRe) ≃ P(R)`. It sends `(eRe)^n` to `(eR)^n = diag(e,…,e)R^n`. So on `GL_n(eRe)` it is `a ↦ a + (1−e)I_n`
    after the standard stabilization, and on Steinberg generators it is the corner inclusion.
  - So the isomorphism of Cor. 5.6.1 is the one the node uses. The same holds for `K_0` and `K_1`, which Weibel
    refers to II.2.7.
  - **Pin:** Weibel III, Cor. 5.6.1–5.6.2, with that one-line identification.
- **Perron–Frobenius.** Standard, not read at source.
  - The statement used: for an irreducible nonnegative matrix, the spectral radius is an algebraically simple
    eigenvalue with a positive eigenvector.
  - The eigenvector can be taken rational, because `A` is rational and `ker(1 − A)` is one-dimensional over `Q`.
- **Cancellation in matricial rings.** As in `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` (refereed PASS,
  a141e77ba). It applies factorwise to a finite product of `U_Q`-type rings.
- **Internal nodes.**
  - `graded-rings-with-degree-one-units-fail-the-k-budget` is applied to `eRe` with unit `e`. `λ ↦ λe` is unital
    because `Q` is central in `R`, and `w` is a unit of degree `1`.
  - `infinitely-generated-symbols-block-fp-elementary-groups` needs `Sym(R)` not finitely generated. Here `{λ, u_e}`
    are symbols of the commuting units `λ` and `u_e` of `R`.
  - `rational-k1-detection-forces-infinite-order-unit-class` is used in item 7(a).
  - Item 4 of `isometric-frames-over-rank-one-bases-fail-the-k-budget` supplies the automatic grading.

## Steps checked

- **Item 1.** `ew = ww'w = we`, so `w = ewe`. `u_e = w + f` has inverse `w' + f`, since `wf = fw = 0`.
- **Item 2.**
  - `C = eRe × fRf` is a unital subring, and `St_N(C) = St_N(eRe) × St_N(fRf)` for `N ≥ 3`.
  - `λ = (λe + f)(λf + e)`, and the three units commute pairwise. That gives
    `{λ, u_e} = {λe+f, u_e}{λf+e, u_e}`.
  - The second factor is the image of `({e,w}, {λf, f}) = (1, 1)`.
  - So `{λ, u_e} ↔ {λe, w}` under (M).
- **Item 3.**
  - `μ_λ[g] = [λg + 1 − g]` is additive on orthogonal sums and invariant under equivalence, by stabilized
    conjugation. So it is a homomorphism `K_0 → K_1`.
  - `t[λ] = n[λe + f]`. The map `λ ↦ λ^t` has finite kernel on `Q^x`.
- **Item 4.** Rescaling by the torsion order gives an exact relation.
- **Item 5.**
  - `x = φ(e)x`, and `pφ(e) = φ(e)`.
  - `w'w = ypx = yx = e`, and `ww' = sφ(e)t = e`.
  - The degrees are right.
- **Item 6 (unconditional).**
  - `(tg)(gs) = φ(g)` and `(gs)(tg) = g`, so `[φ(g)] = [g]` in `K_0(R)`.
  - `φ(g)` is an idempotent over `B`, by (T1).
- **Item 7.**
  - `K_0(U_Q) = Q`, and every class in `[0,1] ∩ Q` is represented by an idempotent. So `[e] = εv` exists.
  - `A[e] = [e]`, and cancellation gives `φ(e) ~ e`.
  - Integer `t, n` come from clearing denominators, with `c ≠ 0`, since otherwise case (a) holds.
  - In (c), `Q^m = ker ⊕ im` when `1` is algebraically simple, so `v ∉ im(1 − A)`.
- **The open example.**
  - `A = [[2,1],[2,3]]` has eigenvalues `1` and `4`, and `ker(A − 1) = Q(1,−1)`.
  - The left fixed functional is `(2,−1)`, with value `1` on `(1,1)`.
  - No nonnegative fixed class exists.
  - Correct.

## Gate Attempt 13: the "no Pimsner sequence" claim is correct

- The argument uses only four things:
  - item 6, where `K_0(B) → K_0(R)` kills `(1 − A)K_0(B)` via the equivalence `(tg, gs)` over `R`;
  - the graded node on the corner;
  - (M);
  - the symbol lemma.
- None of these needs (P).
- "(P) enters only the reading that `K_1` detection forces `det(1 − φ_*) = 0`, and item 7(a) gives that part
  unconditionally" is also correct. If `det ≠ 0`, then `[1_B] ∈ im(1 − A)`, so `[1_R] = 0`, and `K_1` detection
  fails.
- **The answer "yes" to Attempt 10.** It is correctly limited to case (b). There the forced classes are Steinberg
  symbols `{λ, u_e}` of commuting units of `R`, so they lie in the image of `K_2(N, R)` for every `N ≥ 3`.
- **The widened gate** (finitely presented and simple, `Q̄ ⊆ R` unitally, the K-budget). The node needs only
  `Q ⊆ R`, so it applies.

## Fix

- **W1 (title).** "closes every multi-type base whose fixed classes meet the positive cone and span the unit class".
  Item 7(b) uses facts specific to finite products of `U_Q`-type rings:
  - `K_0 = Q^m`;
  - every class in `[0,1]^m ∩ Q^m` is represented by an idempotent;
  - cancellation.

  Items 5–6 are general, but the existence of a fixed idempotent is proved only there. Say "every multi-type
  *matricial* base", as Attempt 13 does.
