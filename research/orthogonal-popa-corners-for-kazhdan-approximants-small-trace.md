---
rg: 2
id: orthogonal-popa-corners-for-kazhdan-approximants-small-trace
kind: claim
title: In an infinite Kazhdan group factor, orthogonal Popa corners for 2-norm approximants of the Kazhdan generators have total trace at most 2(eps-4eta)^-2 times the squared approximation defect on them
distinct_from:
  kazhdan-group-factor-popa-corners-have-vanishing-trace: that bounds a single corner by 4eps^-2(4eta+2delta)^2 through the spectral gap in L^2(M); this bounds whole orthogonal families by 2(eps-4eta)^-2 times the defect squared, with no eta^2 term, through the coarse bimodule.
  kazhdan-generators-admit-no-norm-popa-corners: that is the exact case y_s = lambda_s (no corner below tolerance eps/4); this is the 2-norm quantitative version relevant to weakly dense subalgebras.
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

**ESTABLISHED (unreviewed, lane sk-popa-lgx, 2026-09-13)** by route `orthogonal-popa-corners-kazhdan-small-trace-proof`.

**Statement.** Let `Γ` be an infinite group with Kazhdan pair `(S, ε)`, `M = L(Γ)` with trace `τ`, `y_s ∈ M` for `s ∈ S`, and `a_s = λ_s − y_s`. Let `(p_m, B_m)_m` be a finite or countable family with:
- pairwise orthogonal nonzero projections `p_m ∈ M`;
- finite-dimensional C*-subalgebras `B_m ⊆ p_mMp_m` with unit `p_m`;
- `‖[y_s, p_m]‖ ≤ η` and `dist(p_my_sp_m, B_m) ≤ η` for all `s` and `m`, where `4η < ε`.

Put `P = Σ_m p_m`. Then

`Σ_m τ(p_m) ≤ 2(ε − 4η)^{-2} Σ_{s∈S} ( ‖a_sP‖_2² + ‖Pa_s‖_2² ) ≤ 4|S|(ε − 4η)^{-2} max_s ‖a_s‖_2²`.

**Relative badness on every corner.** A single corner `(p, B)` at tolerance `η < ε/4` satisfies, for some `s ∈ S`,

`‖a_sp‖_2 + ‖pa_s‖_2 ≥ (ε − 4η) τ(p)^{1/2}`.

So on every Popa corner, the relative 2-norm error of the approximants is bounded below by `ε − 4η`.

**Consequence for weakly dense Popa algebras** (the Popa clause of Brown's Question 3, `property-t-factors-contain-weakly-dense-popa-algebras`). Let `A ⊆ L(Γ)` be weakly dense with Popa's local quantization property, and let `y_s ∈ A` be Kaplansky approximants with `‖a_s‖_2 ≤ δ`.
- Every orthogonal family of Popa corners for `{y_s}` at tolerance `η < ε/4` has total trace at most `4|S|δ²(ε − 4η)^{-2}`.
- The approximation error concentrates on the corners where `A` is finite-dimensional.
- Any construction must pay a uniform relative defect there, whatever the scale of the corners.
- For `L(G_X)` (infinite, simple, Kazhdan), take any finite generating set `S` with its Kazhdan constant.

**Comparison with Lemma S.** Lemma S gives `τ(p) ≤ 4ε^{-2}(4η + 2δ)²`. Here:
- the bound has no `η²` term, and for `δ = 0` no corner exists (`kazhdan-generators-admit-no-norm-popa-corners`);
- it holds for orthogonal families;
- it uses the defect only on `P`.

**Model tests.**
- **`y_s = λ_s`:** the right side is `0`, so no corner exists at tolerance below `ε/4`. This is the norm-rigidity claim.
- **Finite `Γ`, no invariant-free representation:** `p = 1`, `B = M` and `y_s = λ_s` violate the bound. The proof needs `Γ` infinite.
- **T1 (`separable-ii1-factors-have-weakly-dense-full-free-group-cstar`) in `L(Γ)`:**
  - the corners `q_j`, `j ≥ m`, serve its first `m` generators exactly, with `η = 0`;
  - T1's generators approximate a generating sequence, not `λ(S)`, so `a_s` refers to Kaplansky approximants inside T1's algebra;
  - the bound says their defect on `Σ_{j≥m} q_j` has squared 2-norm at least `ε²τ(Σ_{j≥m}q_j)/2`, which is `O(2^{-m})`.

  This is consistent.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived:
- the exact transfer ‖aζ‖ = ‖ap‖_2 and ‖ζa‖ = ‖pa‖_2 (orthogonal tensor factors and k_rτ(e_ii) = τ(p_r));
- the one-corner badness (ε−4η)τ(p)^{1/2} ≤ ‖a_sp‖_2 + ‖pa_s‖_2;
- summation over orthogonal corners by normality.
See `research/artifacts/sk-verify-16-2026-09-13-part2.md` §3.
