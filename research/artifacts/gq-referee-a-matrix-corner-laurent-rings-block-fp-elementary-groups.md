# Referee report (gq-referee-a, proof-gap lens): matrix-corner Laurent rings block finitely presented elementary groups

**Reviewed:** `matrix-corner-laurent-rings-block-fp-elementary-groups` and its route `-proof` (lane
gq-deep-adelic-1, a922d082a), read on origin/main.

**Verdict: PASS.** One step in (B) needs a sentence (§2). The node inherits T1 (ABC naturality and
Bass–Heller–Swan) and T2 (Fuglede–Kadison), as it says. Part 5 of `q-algebra-elementary-quotients-contain-gl-n-q`,
`E_N(M_k(S)) = E_{Nk}(S)`, is standard for `N ≥ 3` but was not reviewed by me.

## 1. Part (A)
- **Step 1: homogeneity.** Correct.
  - For homogeneous `a`, `a = a·1` forces `a e_n = 0` for `n ≠ 0`. Then `x = 1` gives `1 ∈ S_0`.
  - A homogeneous unit has a homogeneous inverse, in degree `−d`.
  - `Q` lies in `S_0` and is central.
- **Step 2: skew Laurent.** Correct.
  - `S_n = S_0 v^n`.
  - `σ = v(·)v^{-1}` is an automorphism of `S_0` fixing `Q`.
  - `Σ b_n t^n ↦ Σ b_n v^n` is bijective by the grading, because `v` is a unit.
- **Step 3: the image of `Q^×` in `K_1(S_0)` is not finitely generated.** Correct.
  - (a) Use `det`.
  - (b) `ψ(X) = Δ_M(ρ(X))^M` is multiplicative. It is stable, since
    `Δ_{M+1}(diag(Y,1))^{M+1} = Δ_M(Y)^M`, and it is trivial on the perfect group `E`.
  - Then `[λ] ↦ |λ|`, with image `Q_{>0}`.
- **Step 4.** The hypotheses of `laurent-rational-symbols-block-fp-elementary-groups` are:
  - `Q ⊆ B` unital;
  - `σ` fixes `Q`;
  - `R = B[u^{±1}; σ]`, with `u b = σ(b) u`;
  - the image of `Q^×` in `K_1(B)` is not finitely generated.

  These match the statement exactly (gq-referee-b PASS on that node).
- **Step 5.** Correct: `E_N(R) ≅ E_{Nk}(S)` with `Nk ≥ 3`, and finite normal subgroups correspond.

## 2. Part (B)
- **Step 6: matrix units.** Correct.
  - `u_s^{-1}u_{s'} = u_{s^{-1}s'}`.
  - For `s ≠ s'` in `T`, `s^{-1}s' ∉ Γ'`, so that translate of `C` is disjoint from `C`.
  - The distinct translates are `{tC : t ∈ T}`, so `Σ_t e_tt = 1`.
  - Jacobson's theorem gives `R ≅ M_k(χ_C R χ_C)`.
- **Step 7: the grading.** Correct. `χ_C b u_g χ_C = χ_C b χ_{gC} u_g` vanishes unless `g ∈ Γ'`, and it lies in `R`
  because `χ_C ∈ R`. So `S` is `Γ'`-graded, hence `Z`-graded via `φ`.
- **Step 8: the degree-one unit.** Correct. `u_γ χ_C = χ_C u_γ`, and both composites with `χ_C u_{γ^{-1}}` equal
  `χ_C = 1_S`.
- **Step 9: needs a sentence.** A unital ring homomorphism `ρ` sends `χ_C` to an **idempotent** `e`, not
  necessarily to a projection.
  - An idempotent in a von Neumann algebra is similar to a projection `p`, so `eMe ≅ pMp` as rings, and `pMp` is
    a finite factor.
  - Add this, or require `ρ` to be a `*`-homomorphism.
- **The example.** In the example `χ_C` maps to a projection, since `ρ` is the inclusion into `L^∞ ⋊ Γ`, and
  `μ(C) = 1/k > 0`.

## 3. Consequences
- The virtually-indicable-over-odometer remark is correct as a conditional application, provided `R` contains
  `χ_C` and the `u_g`. It is stated that way.
