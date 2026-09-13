---
rg: 2
id: block-balanced-towers-central-halving-proof
kind: route
title: Half of the equal-rank blocks is a projection commuting exactly with every earlier stage
target: block-balanced-towers-have-central-halving
requires: []
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Direct proof: Sections 3–4 of the artifact (Proposition B and the towers).

1. Put `p_j = μ_{n_j}(Σ_{b ≤ ⌊L_j/2⌋} e^{(j)}_b)`. It commutes exactly with `μ_m(A_m)` for
   `m ≤ m_j`. These images have norm-dense union, so `‖[p_j, a]‖ → 0` for all `a ∈ A`.
2. Every trace of `A` pulls back to a trace of `A_{n_j}`. So
   `τ(p_j) = ⌊L_j/2⌋/L_j ∈ [1/2 − 1/(2L_j), 1/2]`.
3. **Splittings.** If `φ_{m,n} = Σ_b φ^{(b)}` with orthogonal ranges, then
   `e_b φ^{(b')}(a) = δ_{bb'} φ^{(b)}(a) = φ^{(b')}(a) e_b` for `e_b = φ^{(b)}(1)`. Point traces
   of `q_n(C(X_n) ⊗ K)q_n` give `τ(e_b) = rank(e_b)/rank(q_n)`.
4. **Instances, from the source texts on MSI.**
   - Toms 2606.12188v2, lines 331–441: `ϕ_i(a) = (π_1*a ⊗ γ_{i,1}) ⊕ (π_2*a ⊗ γ_{i,2})`, with
     `rank(q_{i+1}) = 2d_i`, so there are two blocks of rank `d_i`.
   - Toms, lines 1255–1300: `ψ^top` is the telescoped diagonal map on the whole
     `s_i`-corner, and `ψ^pt` consists of point evaluations in orthogonal summands. All
     blocks have rank `rank(s_i)`.
   - DHTW 0712.2020: `φ_i = (id ⊗ e_{i+1}) ⊕ (α_{i,[i]} ⊗ f_{i+1})`, with rank-one `e, f` and
     unital `α`.
   - Corners by a finite-stage projection `p` inherit the blocks `φ^{(b)}(p)`, whose
     ranks are equal.
