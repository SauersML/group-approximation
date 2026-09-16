---
rg: 2
id: bf-n-r-twist-invisible-via-braid-resonance
kind: route
title: "Eventual non-resonance of the braid restrictions plus the resonance conjecture for P_k, fed into Lemma 5"
target: bf-n-r-twist-invisible-braid-characters-in-sigma-infinity
requires:
  - bf-n-r-twist-invisible-restrictions-nonresonant
  - pure-braid-bnsr-complements-are-real-resonance-varieties
  - pure-braided-bht-braid-characters-dimension-n-n-minus-1
artifacts:
  - research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md
  - research/artifacts/zp-bf-n-r-twist-invisible-quotient-and-resonance-2026-09-16.md
---

Let `chi = pi^* psi + phi`, with `phi` in `W_0 \ {0}` and `psi` arbitrary. The
last required claim supplies `W`, `W_0` and the restricted characters
`Phi_k(A_{ij}) = phi(type(i, j, k))` of `P_k = PB_k`.

1. Fix `j >= 1`. By `bf-n-r-twist-invisible-restrictions-nonresonant` there is
   `K` such that for all `k >= K`, `k ≡ r mod (n-1)`, the Aomoto complex
   `(A(P_k) ⊗ R, Phi_k ∧)` has `H^i = 0` for `i <= j`. In particular
   `Phi_k != 0` (from `H^0 = 0`), and `Phi_k` is not a real point of
   `R^{<=j}(P_k)`. Resonance is detected over any field containing the
   coefficients, since ranks do not change under field extension.
2. By `pure-braid-bnsr-complements-are-real-resonance-varieties`, applied with
   `m = j` and `n = k`, `Sigma^j(P_k) = S(P_k) \ S(R^{<=j}(P_k; R))`. So
   `[Phi_k]` lies in `Sigma^j(PB_k)` for all such `k`.
3. Part 2, Lemma 5 (artifact `zp-pure-braided-bht-sigma-2026-09-13.md`) is the
   reduction already recorded on the target. It turns step 2 into
   `[chi]` in `Sigma^j(bF_{n,r})`.
4. `j` was arbitrary, and `Sigma^infinity = ∩_j Sigma^j`. So `[chi]` lies in
   `Sigma^infinity(bF_{n,r})`.

Notes.

- Lemma 5 reuses steps (b)–(d) and (f) of part 2, Theorem 3: Meinert's criterion
  on a band of the Skipper–Wu Stein space. That is the argument of the
  established `bf-n-r-twist-detected-characters-lie-in-sigma-infinity-proof`,
  with the central-element step replaced by the hypothesis on `Sigma^j(PB_k)`.
  The cube stabilizers are conjugates of pure braid groups on the feet. The
  restriction of `chi` to such a stabilizer is `Phi_k` up to the identification
  of the feet with the leaves of a forest.
- The caution on the target, that first-leaf characters factor through
  `Z wr_Omega F_{n,r}`, gives no obstruction to this route. By artifact §3
  (Proposition 3, Mendonça arXiv:1709.06303 Theorem B and Cornulier's criterion
  as quoted there), that quotient is finitely presented and all its lamp
  characters lie in `Sigma^2`.
- Evidence for the first requirement, and the reasons the generic-weight
  vanishing theorems cannot prove it, are in artifact §§5–7 of
  `zp-bf-n-r-twist-invisible-quotient-and-resonance-2026-09-16.md`.
