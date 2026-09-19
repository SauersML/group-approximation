---
rg: 2
id: rank-five-degree-one-two-cell-configuration-is-a-core
kind: claim
title: The rank-5 degree-one configuration (C2) is a genuine two-cell core, so pi_1(C) -> G is injective for w = yxYXXyyxYXYxYYxyXy. G is F_4 x|_phi Z, the free fibre of pi_1(C) is exhausted by windows that grow by a free factor of rank 2, and a train-track representative of phi turns the window induction into a finite fixed-point certificate
distinct_from:
  degree-one-two-cell-configs-evade-character-tests: that constructs (C2), shows no character kills c, g in P and g not in H, and leaves open whether pi_1(C) -> G is injective. This proves the injectivity, so (C2) is a core and not just a configuration.
  degree-one-two-cell-cores-with-ab-nonzero-exist: that proves a rank-3 ab != 0 core via a finite cover and Brodskii-Howie, and that core is killed by a character. This core has rank 5, no finite cover of index below 9 carries it, the proof is by a train track of the fibre monodromy, and no character kills its row c.
  two-cell-ab-nonzero-admissible-needs-g-in-conj-closure: that proves g in P and the absence of killing characters are necessary for admissibility. This supplies a core that meets both necessary conditions, so neither can close the ab != 0 case.
artifacts:
  - research/rank-five-degree-one-two-cell-configuration-is-a-core-proof.md
  - experiments/c2-free-by-cyclic-2026-09-18/RESULTS.md
  - experiments/c2-free-by-cyclic-2026-09-18/verify_core.py
  - experiments/c2-free-by-cyclic-2026-09-18/cert.py
  - experiments/c2-free-by-cyclic-2026-09-18/tt2.py
  - experiments/c2-free-by-cyclic-2026-09-18/fbc.py
  - experiments/c2-free-by-cyclic-2026-09-18/fold2.py
  - experiments/c2-free-by-cyclic-2026-09-18/tt_search.py
  - experiments/c2-free-by-cyclic-2026-09-18/run5.py
---

**ESTABLISHED** via `rank-five-degree-one-two-cell-configuration-is-a-core-proof` (unreviewed,
computer-assisted). The proof reduces injectivity to one finite certificate. The certificate is a
fixed point of an explicit folding step on a labelled graph with 106 vertices, and
`verify_core.py` replays it in about a second. It is not a finite-depth check: the fixed point
closes an induction over all window lengths.

## Statement

Take configuration (C2) of `degree-one-two-cell-configs-evade-character-tests`:
- the word is `w = yxYXXyyxYXYxYYxyXy`;
- the graph `Γ` has vertices `0..4`, with `v_0 = 3`, `v_1 = 0` and basis
  `a = x⁻¹yxy⁻¹x`, `b = x⁻¹y³x`, `c = x⁻¹y⁻¹xyx`, `d = y`, `e = xyx⁻¹`;
- the cells are `u_0 = d e⁻¹ b c b⁻¹ a⁻¹ d⁻² e d` and `u_1 = b c b⁻¹ a⁻² b d⁻¹ c b⁻¹ d`.

Then `C = Γ ∪ e_0 ∪ e_1` is a two-cell core: `π_1(C) = ⟨a,b,c,d,e | u_0, u_1⟩ → G = ⟨x,y | w⟩`
is injective. Here `χ(C) = 5 − 9 + 2 = −2`, and the image `H` is a degree-one `(a,b) = (1,2)`
base with `ab ≠ 0`.

The proof also gives the following structure:
1. `G = F_4 ⋊_φ ⟨y⟩` with `F_4 = ⟨p,q,r,s⟩ = ⟨x_{-2},x_{-1},x_0,x_1⟩`, where `x_j = y^j x y^{-j}`
   and `φ: p↦q, q↦r, r↦s, s↦r²s⁻¹qp⁻¹r⁻¹s`.
2. `K_C = ker(π_1 C → Z)` is free on `{a_j, b_j : j ∈ Z} ∪ {c_3, e_3, e_4}`. Here
   `g_j = d^j (g d^{-sh(g)}) d^{-j}` with shifts `sh(a) = sh(c) = 0`, `sh(b) = 3`,
   `sh(e) = 1`, and `π_1(C) = K_C ⋊ ⟨d⟩`.
3. The windows `T_M = ⟨c_3, e_3, e_4, a_0..a_M, b_{-1}..b_M⟩` (rank `2M+6`) exhaust `K_C` up to
   `d`-conjugation, and `T_{M+1} = d T_M d⁻¹ ∗ ⟨a_0, b_{-1}⟩` for `M ≥ 4`.
4. With `θ: s ↦ qsr`, the map `ψ = θφθ⁻¹: p↦q, q↦r, r↦qsr, s↦s⁻¹p⁻¹r⁻¹` is a train-track map
   of the rose, with gates `{p,r,s}`, `{p⁻¹,q⁻¹,r⁻¹}`, `{q,s⁻¹}`. For `M ≥ 8` there are
   folded graphs `X_M` representing `θΦ(T_M)` that are legal outside radius 12 of the base. They
   all have the same radius-12 ball, with 106 vertices, and that ball is a fixed point of the fold
   step with no rank loss.

## Consequences for the lane

- The `ab = 0` step for degree-one two-cell **cores** is false in a strong form. Cores with
  `ab ≠ 0` exist (already known at rank 3), and (C2) is one that meets every necessary condition
  for admissibility proved so far:
  - no character over any field kills `c`;
  - `g ∈ P = ⟨g^k H g^{-k}⟩`;
  - `c` is unimodular over `Z[Q]` for every finite image tried.
  So the proposed step "for every `ab ≠ 0` two-cell core some character kills `c`" is refuted by
  an actual core, not only by a configuration.
- The pair `(H, G)` is therefore the first concrete candidate for an admissible base with relative
  defect `ρ(H,G) = 1` (`ρ ≤ n(C) − 1 = 1` by `relative-realization-is-relative-efficiency`). It is
  admissible exactly when the row `c` is unimodular over `ZG`
  (`two-cell-core-deletions-need-a-unit-fox-coefficient`). It is:
  `admissible-ab-nonzero-two-cell-base-exists` gives an explicit certificate. That claim also
  records the resulting dichotomy: either `RP(H,G)` holds, or `Γ_{ℵ_1}(H,G)` is an
  Eilenberg–Ganea counterexample.
- The method is new for this lane: a train-track fixed-point certificate for one-sided windows of
  an HNN fibre. It needs three things: a free-by-cyclic `G` (both exponent sums of `w` zero,
  with extreme levels occurring once), a shift lemma for the fibre basis, and a rose train track
  for the monodromy after a small change of basis. It has no rank bound. The
  finite-cover and Brodskii–Howie route used at rank 3 needs `r ≤ 3`.

## Attempts

- **w11-048, 2026-09-18.** Dead routes, each for a precise reason:
  - The Bass/Stallings-pullback criterion for the HNN splitting `π_1(C) = HNN(Ω, d)` fails because
    `Ω ∩ φ(Ω)` is larger than the edge group in the image, so it does not certify injectivity.
  - C'(1/6) small cancellation fails, since `yxY` and `yxYX` are pieces.
  - A finite trap graph would have to contain `A` in its fundamental group.
  - Bounded-cancellation ball induction in the original basis needs a radius-`7R` ball to control
    a radius-`R` ball, so it diverges. The train track removes exactly this loss, because legal
    paths never cancel.
  - `φ⁻¹` has no rose train track among conjugates by products of two Nielsen moves, while `φ`
    does. So the positive direction is used.
