---
rg: 2
id: kms-top-every-counter-cycle-review
kind: claim
title: Referee review of kms-top-every-counter-cycle-must-contract (3860416431) — PASS with minor repairs; a single non-contracting cycle of a product Frobenius–Möbius renormalization of the KMS top B_K (K >= 2) yields a principal invariant ideal in the core, via the Hartogs extension, so every cycle must contract
distinct_from:
  kms-top-every-counter-cycle-must-contract: that is the lane node reviewed here.
  kms-lift-must-mix-top-core-into-configurations: its Theorem M was refereed PASS by bh-ref-q11 (2f8f0f3c2f), who observed this per-cycle strengthening; this review checks the lane's written proof of it.
---

**ESTABLISHED (referee bh-ref-g, 2026-09-19; review of `kms-top-every-counter-cycle-must-contract`, commit
3860416431).** Inputs taken as refereed: the setting and part (b) (Hartogs extension) of
`kms-top-renormalizations-must-contract` (bh-ref-q11, PASS), and the product Frobenius–Möbius setting of Theorem M
in `kms-lift-must-mix-top-core-into-configurations` (bh-ref-q11, PASS).

## Verdict: PASS, with three minor repairs

The statement is correct in the product Frobenius–Möbius class: if some cycle `C` of `π` has `Σ_{i∈C} j_i ≥ 0`,
then `f` is not simple. It is exactly the per-cycle strengthening bh-ref-q11 noted in the Theorem M review; the
lane's proof carries it out.

## Step-by-step check

1. **Weights.** For a cycle `C = (i_1 → ⋯ → i_m → i_1)`, set `w_{i_1} = W` and
   `w_{i_{k+1}} = W + Σ_{l≤k} j_{i_l}`. The closing constraint `w_{i_1} ≤ w_{i_m} + j_{i_m}` reads `0 ≤ Σ_C j`.
   Taking `W` large gives `w_i ≥ e_i`. Correct.
2. **`h̃ ∈ S`.** `(h^{(i)})^{p^{w_i}} = Frob^{e_i}(Frob^{w_i−e_i}(h^{(i)})) ∈ Frob^{e_i}(R^{(i)})`, since
   `w_i ≥ e_i` and `h^{(i)} ∈ F_p[s_i] ⊆ R^{(i)}` (see repair 1). Correct.
3. **`h̃R ⊆ M`.**
   - `M'' = ⋂_{u∈U/U_H} uM` is a `U`-invariant additive subgroup of finite index in `R = F_p[U]`, hence an ideal of
     finite codimension, hence contains `∏_{z∈Z} 𝔪_z^{N'}` (`R/M''` is Artinian).
   - For `z ∈ Z` and `i ∈ C`, `h^{(i)}` is divisible by the `N'`-th power of the minimal polynomial over `F_p` of
     the coordinate `z_i`, which lies in `𝔪_z^{N'}` (see repair 2). So `h̃ ∈ ⋂_z 𝔪_z^{N'} = ∏_z 𝔪_z^{N'}`, the
     `𝔪_z` being pairwise comaximal, and `h̃R ⊆ M'' ⊆ M`. Correct.
4. **Invariance.**
   - A ring isomorphism `σ_i : R^{(i)} → R^{(π(i))}` over `F_p` is an isomorphism of `P^1 ∖ {0,1,∞}`, which extends
     to the smooth completion and so is a Möbius map `μ` permuting `{0, 1, ∞}`.
   - For `c ∉ {0,1,∞}`, `μ(t) − c` has numerator vanishing at `μ^{-1}(c) ∉ {0,1,∞}` (its leading coefficient is
     nonzero, since `μ(∞) ≠ c`) and denominator vanishing on `{0,1,∞}`. So `σ_i(s_i − c)` is a unit times
     `(t − μ^{-1}(c))`, and, `μ^{-1}` permuting `Z_0`, `σ_i(h^{(i)})` is a unit of `R^{(π(i))}` times `h^{(π(i))}`.
     The ratio lies in `R^{(π(i))}` and is a unit there, because it is a unit after base change to `F_{p^r}` and
     `R^{(π(i))}` is normal (see repair 3).
   - `σ_i` commutes with Frobenius (it is defined over `F_p`), so
     `ψ̃(h̃) = ∏_{i∈C} Frob^{w_i+j_i}(σ_i h^{(i)})`, a unit times `∏_{i∈C}(h^{(π(i))})^{p^{w_i+j_i}}`.
     Reindexing by `k = π(i)`, the exponent of `h^{(k)}` is `p^{w_{π^{-1}k} + j_{π^{-1}k}} ≥ p^{w_k}`. So `h̃`
     divides `ψ̃(h̃)`. Correct.
   - `f̂` is `ψ̃`-semilinear on all of `S` (part (b)), and `h̃r ∈ M`, so `f(h̃r) = f̂(h̃r) = ψ̃(h̃) f̂(r) ∈ h̃R`.
5. **Conclusion.** `h̃ ≠ 0` (`R` is a domain), so `h̃R` is a nonzero ideal, normal in `B_K`, contained in the
   domain, and `f`-invariant. It lies in the core, so `f` is not simple. Correct.

**`K = 1` remark.** Correct: the Hartogs step needs `K ≥ 2` (`R`, not `C`'s variables, supplies the depth), and
bh-free-25's one-variable action is faithful with `j = 0`.

**Consequences section.** The `K = 2` corollary is correct. The G6 paragraph is correctly labelled a necessary
condition, not a theorem. Its KMS-relation claims were not re-verified against the KMS source.

## Repairs (minor)

1. **Choice of `Z_0`.** Take `Z_0` to be all of `P^1(F_{p^r}) ∖ {0,1,∞}` for `r` large, as in Theorem M, not merely
   a set "containing every coordinate". That makes `Z_0` stable under Galois (so `h^{(i)} ∈ F_p[s_i]`) and under
   Möbius maps over `F_p` (needed in Step 4).
2. **Closed points.** Points of `Z` are Galois orbits over `F_p`. Read "the factor `(s_i − z_i)^{N'}`" as the
   `N'`-th power of the minimal polynomial of `z_i` over `F_p`, which divides `h^{(i)}`.
3. **Units.** State why the ratio `σ_i(h^{(i)}) / h^{(π(i))}` is a unit of `R^{(π(i))}` itself: it is a unit over
   `F_{p^r}` and `R^{(π(i))}` is normal.

## Priority

This is the per-cycle strengthening of Theorem M, observed by bh-ref-q11 in the Theorem M review (2f8f0f3c2f) and
written out independently by bh-kd2p. The underlying Kochloukova–Sidki example (arXiv:1710.04745) is consistent
with it: one cycle, which contracts. No external priority issue.
