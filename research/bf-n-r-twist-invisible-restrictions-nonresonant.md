---
rg: 2
id: bf-n-r-twist-invisible-restrictions-nonresonant
kind: claim
title: "Braid restrictions of full-twist-invisible characters of bF_{n,r} are eventually non-resonant in every degree"
distinct_from:
  braid-arrangement-higher-resonance-varieties-computed: that claim asks for the full list of components of R^m(P_n) at fixed n; this one asks only that the specific characters Phi_k avoid R^{<=j}(P_k) once k is large, and does not need the components.
artifacts:
  - research/artifacts/zp-bf-n-r-twist-invisible-quotient-and-resonance-2026-09-16.md
  - research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md
---

Let `n >= 3`, `r >= 1`, `d = n - 1`, and let `phi` be a nonzero element of the
full-twist-invisible subspace `W_0` of `Hom(N, R)^{F_{n,r}}`
(`pure-braided-bht-braid-characters-dimension-n-n-minus-1`). Write
`Phi_k(A_{ij}) = phi(type(i, j, k))` for the restricted character of the pure
braid group `P_k = PB_k`.

Claim: for every `j >= 1` there is `K = K(phi, j)` such that for all
`k >= K` with `k ≡ r mod d`,

    H^i(A(P_k) ⊗ R, Phi_k ∧) = 0   for 0 <= i <= j,

where `A(P_k)` is the Orlik–Solomon algebra of the braid arrangement and
`Phi_k` is read as the degree-one element `sum_{i<j} Phi_k(A_{ij}) e_{ij}`.
Equivalently, `Phi_k` lies outside the real points of
`R^{<=j}(P_k) = R^0 ∪ ... ∪ R^j`.

## Attempts

- 2026-09-16, computation (artifact
  `zp-bf-n-r-twist-invisible-quotient-and-resonance-2026-09-16.md`, §7;
  scripts in `experiments/zp-bf-n-r-first-leaf-star-resonance-2026-09-16/`).
  Ranks of the Aomoto complexes mod `2^31 - 1` and `10^9 + 7`, for `n = 3, 4`
  and `k <= 9`:
  - random points of `W_0`;
  - the part-2 example;
  - the first-leaf characters.
  A reported zero is exact over `Q`, because rank mod `p` is at most rank over
  `Q`. A nonzero value is evidence only. In every case the first resonant
  degree grows with `k`; no bounded resonant degree appears.
- 2026-09-16, first-leaf characters (proved, artifact §§1–2, 5). The elements
  of `W_0` with `PPP = PPE = PEP = 0` form a `(d-1)`-dimensional subspace. They
  factor through a surjection `bF_{n,r} -> Z wr_Omega F_{n,r}` that records how
  the first strand winds. In symmetric coordinates their restriction is
  supported on the edges `{1, j}` and `{j, infinity}` for the `s` indices `j` in
  the support, and `s >= 2 floor((k-2)/d)`.
  - Every family of pencils whose span contains the restriction has pencil
    depth at least `s/2` (Proposition 5).
  - So the upper-bound direction of the pencil-depth conjecture in
    `braid-arrangement-higher-resonance-varieties-computed` would prove this
    claim on that subspace.
  - Computed: the first resonant degree is `s/2` whenever the computation
    reached degree `s/2`. In the other cases the complex vanishes in every
    degree computed, all below `s/2`. The vanishing below `s/2` is certified
    over `Q`. The nonvanishing at `s/2` is mod-`p` evidence only.
- Where a direct proof dies:
  - Proposition 6: every interval of `td + 1` consecutive strands has weight
    `sum Phi_k(A_{pq}) = 0` on `W_0`. So the hypotheses of Yuzvinsky-type
    nonresonance vanishing theorems (nonzero weights on dense edges, or on the
    dense edges at a hyperplane at infinity) fail for every `phi` in `W_0`.
    Those theorems cannot give the claim.
  - No fixed `k` works for all `j`. A first-leaf restriction lies in one
    pencil subspace `L_U` with `|U| = s + 2`, so
    `pure-braid-sunflower-characters-obstruct-bnsr-invariants` gives
    `[Phi_k] ∉ Sigma^{s-1}(P_k)`. It is also resonant in some degree
    `<= s - 1`. This uses the retract of Aomoto complexes noted on
    `pure-braid-bnsr-complements-are-real-resonance-varieties`: `M_{0,U}` has
    nonzero Euler characteristic and dimension `s - 1`. So `K(phi, j)` must
    grow with `j`.
- The `n = 3`, `r` even example of part 2 gives further evidence that `K`
  depends on `j`. Mod `p` it is resonant in degree 1 at `k = 4` and in degree 2
  at `k = 6`. The nonvanishing is evidence only; the certified vanishing is
  `H^{<=3} = 0` at `k = 8`.
- Use: with `pure-braid-bnsr-complements-are-real-resonance-varieties` this
  claim proves `bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`
  (route `bf-n-r-twist-invisible-via-braid-resonance`).
