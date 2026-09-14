---
rg: 2
id: finite-dimensional-combs-generate-popa-algebras
kind: claim
title: An increasing union of C*-algebras with full corner projections that commute with earlier stages, compress them to simple finite-dimensional algebras, and jointly separate their points is a Popa algebra
distinct_from:
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that builds weakly dense residually finite-dimensional subalgebras through exactly central corners, which kills simplicity; this is the abstract criterion saying which corner systems give simple QD algebras with local quantization.
  kazhdan-generators-admit-no-norm-popa-corners: that is an obstruction on corners serving Kazhdan generators; this is a sufficient condition for a Popa algebra, with no group input.
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

**ESTABLISHED (sk-verify-16 PASS, sk-verify-24 PASS; lane sk-popa-lgx, 2026-09-13)** by route `finite-dimensional-combs-generate-popa-algebras-proof`.

**Definition (comb).** Let `A` be a unital C*-algebra, the norm closure of an increasing union `A_1 ⊆ A_2 ⊆ ⋯` of unital C*-subalgebras. A *comb* for `A` is a sequence of projections `e_i ∈ A_{i+1}` with:
- **(C1) commutation:** `e_i` commutes with `A_i`, and `e_iA_ie_i` is a simple finite-dimensional algebra (a full matrix algebra with unit `e_i`);
- **(C2) separation:** for every `i` and every nonzero `x ∈ A_i` there is `j ≥ i` with `e_jxe_j ≠ 0`;
- **(C3) fullness:** each `e_i` is full in `A`, i.e. there are `v_1, …, v_r ∈ A` with `Σ_l v_le_iv_l* = 1`.

**Statement.** If `A` has a comb, then `A` is a Popa algebra in the Brown–Dykema sense (arXiv:math/0207005, introduction): unital, simple, and for every finite `𝔉 ⊆ A` and `η > 0` there is a nonzero finite-dimensional `B ⊆ A` with unit `e`, `‖[x,e]‖ < η` and `dist(exe,B) < η` for `x ∈ 𝔉`. In particular `A` is quasidiagonal. Every `A_i` is residually finite-dimensional.

**Use for Brown's Question 3** (`property-t-factors-contain-weakly-dense-popa-algebras`). A II_1 factor `M` contains a weakly dense Popa algebra as soon as it contains a weakly dense unital C*-subalgebra with a comb.

Two constraints apply in a property (T) group factor `L(Γ)` with Kazhdan pair `(S, ε)`:
- **Corner traces.** Each `e_j` is an exact Popa corner for all of `A_j`. So `orthogonal-popa-corners-for-kazhdan-approximants-small-trace` gives `τ(e_j) ≤ 4|S|ε^{-2} dist_2(λ(S), A_j)²`: the teeth of a weakly dense comb have vanishing trace.
- **Fullness cost.** In a II_1 factor, any witness `Σ_lv_le_iv_l* = 1` has `1 = τ(Σ_lv_le_iv_l*) ≤ Σ_l‖v_l‖²τ(e_i)`, so `Σ_l‖v_l‖² ≥ 1/τ(e_i)`. Vanishing teeth need ever larger fullness witnesses.

**Model tests.**
- **UHF `M_{2^∞}`:** take `A_i = M_{2^i}` and `e_i = 1_{M_{2^i}} ⊗ f ∈ M_{2^i} ⊗ M_2 = A_{i+1}`, with `f` a rank-one projection. `e_iA_ie_i ≅ M_{2^i}`, `e_j(x⊗1)e_j = x ⊗ f′ ≠ 0` for `x ≠ 0`, and `e_i` is full. `A` is a Popa algebra, as expected.
- **T1's algebra fails:** the corners `q_j` of `separable-ii1-factors-have-weakly-dense-full-free-group-cstar` reduce the generators exactly but are not in the algebra. Adding them would make them central, not full, so there is no comb. That algebra is not simple, consistent with the criterion.
- **`A = C ⊕ C`,** with `A_i = A` and `e_i = (1,0)`: (C1) holds, but (C2) fails for `x = (0,1)` (`e_jxe_j = 0`) and (C3) fails too. `A` is not simple. Step 3 of the proof uses both hypotheses.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: e_jxe_j is a unital *-homomorphism on A_i (RFD, hence QD, passing to the limit); local quantization with B = e_iA_ie_i; simplicity via J ∩ A_i ≠ 0, the simple tooth algebra and fullness. The model tests are correct. See `research/artifacts/sk-verify-16-2026-09-13-part3.md` §8.

**Review (sk-verify-24, 2026-09-14): PASS**, an independent second node-level review (`research/artifacts/sk-verify-24-2026-09-14.md` §2).
- **Definition at source.** The Popa algebra definition was read verbatim in the Brown–Dykema e-print (arXiv:math/0207005 `pa.tex` l.219–226, introduction), and the statement matches.
- **Re-derived.**
  - Multiplicativity of `ρ_j`, RFD stages, and QD of the limit.
  - One index serving all of `𝔉`, with `‖[x,e_i]‖ ≤ 2‖x−x′‖` and `‖e_ixe_i − e_ix′e_i‖ ≤ ‖x−x′‖`.
  - Some `J ∩ A_i ≠ 0` by isometry of injective *-homomorphisms; then `K = J ∩ e_jA_je_j` is a nonzero ideal of a full matrix algebra, so `e_j ∈ J` and, by fullness, `1 ∈ J`.
  - The model tests.
- The status line no longer says "unreviewed".
