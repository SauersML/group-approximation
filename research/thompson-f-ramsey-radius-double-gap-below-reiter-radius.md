---
rg: 2
id: thompson-f-ramsey-radius-double-gap-below-reiter-radius
kind: claim
title: In Thompson's F, the coarse Reiter radius is not bounded by any bounded tower wrapped around two compositions of the Ramsey function (RGAP₂)
distinct_from:
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, about the fine function R̃; this compares only the precision-1/2 Ramsey radius R with the coarse Reiter radius CR, and implies ¬AMP by Corollary 3 of thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that is the established sandwich RGAP₂ ⇒ ¬AMP ⇒ RGAP₁; this is its strong end, left open.
  thompson-f-folner-function-exceeds-every-tower: that says CR is not elementary; this says CR is not elementary even relative to two compositions of R, which is a statement about R being small.
---

**OPEN.** Notation is as in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`: `R = R_{F,{x_0,x_1}}`, `CR` is
the coarse Reiter radius, and values lie in `[0, ∞]`.

**Statement (RGAP₂).** For every integer `D ≥ 0` there is an integer `M ≥ 1` with

`CR(M) > exp_D(R(exp_D(A + 4M)) + 4M)`, where `A = exp_D(R(exp_D(4M+1)) + 4M)`.

**Consequences.** It implies ¬AMP (`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`), and hence
that F is amenable. This is Corollary 3 of the sandwich.

**Why it is a genuine reformulation.** It mentions neither `R̃` nor any precision other than 1/2 and 1. It asks
that, in F, "every 2-coloring of `B_n` is balanced by some measure" be reachable at radii non-elementarily smaller
than "one measure is moved by at most 1 by all of `B_M`", even after composing the former twice. This is a
quantifier-exchange problem, `∀E ∃ν` against `∃ν ∀E`, with no amplification left in it. The weaker end, RGAP₁,
is necessary for ¬AMP. So if some fixed tower bounds `CR` in terms of `R ∘ exp_E`, the whole Ramsey-amplification
route is dead.

## Attempts

- **2026-09-18 (swarm-0917-w9-w9-f-last1, host-geometry).** The first lower bound on `R` that holds at every `m`,
  plus an obstruction to the refuting direction. RGAP₂ itself stays OPEN.
  - *Lower bound (established, new node `thompson-f-ramsey-radius-is-at-least-exponential`).* One coloring does it:
    `E = {y : y⁻¹ has no breakpoint at 1/2}`. Four words in `B_{2r+3}` send `1/2` to a given point `p` of the
    Schreier ball `P(r)` with breakpoint jumps `0, 1, 2, 3`. So any measure that balances `E` for `B_{2r+3}` must
    make `y⁻¹` break at `p` with probability at least `1/4`, for every `p ∈ P(r)`. Ping-pong on `[1/2, 3/4)` gives
    `|P(r)| ≥ 2^{⌊r/2⌋}`, and the data show `|P(r)| = Fib(r+3) − 2` for `r ≤ 12`. Hence `R(m) ≥ 2^{m/4−6}` for all
    `m`, unconditionally.
  - *What it does to this node.* Both inner compositions `R(exp_D(·))` in RGAP₂ are now at least exponential in
    their argument. RGAP₂ still asks `CR` to beat a bounded tower over them. The lower bound makes RGAP₂ harder to
    satisfy, not easier, and it cannot refute RGAP₂ either. The method caps out at exponential: forcing at a finite
    set `T` of points constrains only `B_m·T`, and `|B_m| ≤ 4·3^{m−1}` (route, Remark 3). So lamp forcing will not
    separate `R` from `CR` by a tower in either direction.
  - *Refuting direction, killed class: selector coding of the quantifier swap.* To refute RGAP₂ one needs roughly
    CRE (`∃ν ∀E` at elementary cost over `∀E ∃ν`). The natural attempts encode `k` colorings `E_1, …, E_k` of
    `B_n` into one coloring `E = {y : π(y) ∈ E_{σ(y)}}` of a larger ball. Here `σ` is a selector coordinate and `π`
    a projection, taken from one of three sources:
    - a lamp of a wreath-like subgroup;
    - a commuting rigid copy `F_{[0,1/2]} × F_{[1/2,1]}`;
    - the translation class of a far-away element.

    Then one applies single-set Ramsey once. The invariant is the family of conditional push-forwards
    `ν_i = π_*(ν | σ = i)`. Whenever `σ` is `B_m`-invariant on `supp ν`, balancing `E` controls only the weighted
    average `Σ_i P_ν(σ=i)·(δ_gν_i(E_i) − δ_{g′}ν_i(E_i))`. Every member dies at the same step: extracting one
    measure that balances all `E_i`. The Ramsey measure may choose a different `ν_i` for each `i`, and that returns
    exactly the `∀E ∃ν` information one started with. Non-invariant selectors add cross terms that are again
    controlled only in aggregate. This extends the w8-follow death of translation coding on
    `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead` to all selector and product codings.
  - *Remaining shape.* A coarse-Reiter failure at `B_M` has a minimax dual: an adversary mixture over pairs
    `(f, g)` with `f` a test function. Supporting that mixture needs about `|B_M|` test functions, and Towsner's
    scheme pays one `R̃`-composition per function. Any refutation of RGAP₂ must break this per-function cost with a
    coupling argument that no single coloring detects. This lane did not find one.
- **2026-09-18 (swarm-0917-w10-w10-f-last1, reframing).** The colorings are removed from the problem. RGAP₂ stays OPEN.
  - *Established (new node `ramsey-functions-are-pairwise-reiter-radii`).* A second minimax, over the test functions,
    turns Moore's `R̃(m, ε, l)` into an exact weighted Reiter radius for `l` pairs of measures `(α_i, β_i)` on `B_m`.
    For one pair, `PR_c(m)` is the least `n` such that every `α, β ∈ P(B_m)` has some `ν` with window `n` and
    `‖αν − βν‖₁ < c`. Then `PR_c(m) ≤ R(m) ≤ PR_1(m)` for every `c > 3/2`, with no composition. `CR(M)` is the same
    radius for all `|B_M|` point pairs `(δ_g, δ_e)` at once, against an adversary weighting. So
    PGAP_1 ⟹ RGAP₁ ⟹ PGAP_c, where PGAP_c is RGAP₁ with `R` replaced by `PR_c`.
  - *What this changes.* The `∀E ∃ν` against `∃ν ∀E` swap described in this node's body costs nothing for a fixed pair,
    by minimax. The whole content of RGAP₁ and RGAP₂ is **one pair of measures against all point pairs of `B_M`
    simultaneously**. There is no coloring left. Every lower bound on `R` must exhibit one pair `(α, β)` that no
    measure of window `n` brings within `3/2` in ℓ¹. By clause (D), such a pair has no point mass and does not commute:
    one-sided pairs and commuting pairs are solved at window `9m` in every group, by Cesàro averages.
  - *Obstruction to window-level threshold amplification.* In `F_2`, clause (E) gives `PR_1(1) = ∞` while `R(1) = 3`.
    So no group-independent bound `PR_1(m) ≤ h(R(m))` holds. Moving from threshold `3/2` to threshold `1` needs
    Towsner's compositions (`R̃(m, 1/2) ≤ R³(m)`) and cannot be done at the same window. This is the pair-level form of
    the window-preserving decoupling kill on `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`.
  - *Refuting direction, killed class: marker coding of point pairs into one pair.* To kill the route one would need
    `CR ≤ exp_E(PR_c(exp_E ·))`, that is, the `|B_M|` point pairs packed into one measure pair.
    - *The coding.* Take `α = Σ_g w_g δ_{c_g g}` and `β = Σ_g w_g δ_{c_g}` with markers `c_g ∈ B_m`. Dually, the single
      test function would have to satisfy `f(c_g y) = h_g(y)/w_g`, where `(h_g)` is a coarse certificate.
    - *Where it dies.* The positivity region must contain `I_{m,n} ⊇ B_{2m}` for `n ≥ 3m`, and then
      `c_{g′}⁻¹c_g ∈ XX⁻¹`. The marked translates overlap, and consistency forces the `h_g/w_g` to be translates of one
      function. Those are the translate-coherent certificates, which are exactly the Ramsey dual of
      `small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2`.
    - *The invariant.* Translate coherence. Every marker coding dies at the pigeonhole `c_{g′}⁻¹c_g ∈ XX⁻¹`.
  - *Remaining shape.* A refutation must pack many point pairs into one non-commuting measure pair without markers.
    A proof must find, in `F`, a scale at which every single pair is solvable non-elementarily earlier than all point
    pairs jointly. Neither was found.
- **2026-09-18 (swarm-0917-w10-w10-f-follow, operator-algebras).** The CR side of RGAP₁ is reduced to one
  eigenvalue. RGAP₂ itself stays OPEN.
  - *Established (new node `coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue`, holds in every group).*
    `h(M) ≤ WR(M) ≤ CR(M) ≤ h(2J_M) + J_M` with `J_M = ⌈16kM² ln 2⌉`. Here `WR` freezes the test weight to the
    lazy-walk law `q_N`, and `h(N)` is the least `r` at which `Q^N` compressed to `ℓ²(B_r)` has top eigenvalue at
    least 1/2. The proof uses a Bhattacharyya bound, log-convexity of return moments, and squaring back. So RGAP₁ is
    equivalent to its spectral form SGAP₁ and its single-weight form WGAP₁, because the quadratic change of window is
    absorbed by the tower.
  - *What a kill now needs.* To show that the costly-amplification route is dead (CRE), it suffices, and by (3) is
    also necessary, to prove RRET: for some `E` and every `N`, some unit `η ≥ 0` on `B_n` with
    `n = exp_E(R(exp_E N))` has `⟨η, Q^N η⟩ ≥ 1/2`. This is one "Ramsey balance forces an ℓ² return" statement.
  - *Calibration and killed class.* Time-shift pairs `(q_i, q_j)` of the walk law are ℓ¹-balanced in every group,
    including `F_2`, where `h(N) = ∞` for `N ≥ 13` because `‖Q‖ < 0.947`. So no RRET argument can get its pairs from
    the walk itself.
  - *Data.* Eigenvalue certificates to radius 9 for `F` and radius 8 for `F_2`: `h(1..5) = 0, 1, 1, 2, 2` in both,
    and `h_F(6) = 3`. These are loose at small windows (`CR_F(1) = 5`, from the LP node) and matter only
    asymptotically.
- **2026-09-18 (swarm-0917-w11-w11-f-last1, reframing).** The second composition in RGAP₂ is identified and split
  off as a hypothesis of its own. RGAP₂ itself stays OPEN.
  - *Established (new node `thompson-f-ramsey-radii-in-the-elementary-degree-order`).* The node works in the preorder
    `φ ≼ χ` iff `φ ≤ exp_E ∘ χ ∘ exp_E` for some `E`. Put `ψ(t) = R̃(t, 1/t)` and `ψ_l(t) = R̃(t, 1/t, l)`.
    - One Reiter witness balances every family of test functions at once, so `R̃(m, ε, l) ≤ F(m, ε)` for every `l`.
    - With (b) and (c) of the sandwich, `ψ_l ≈ CR` for every `l ≥ 2`, and `R ≼ ψ ≼ CR ≼ ψ∘ψ`.
    - AMP ⇔ `ψ ≼ R`.
    - With SFC := `CR ≼ ψ` and SFG its negation, RGAP₁ ⇔ ¬AMP ∨ SFG, and RGAP₁ ∧ SFC ⇒ ¬AMP.
  - *What it does to this node.* The double composition of `R` in RGAP₂ is exactly the cost of a second test
    function: `CR ≈ ψ_2` but only `CR ≼ ψ_1∘ψ_1`. RGAP₂ can be traded for RGAP₁ plus SFC, a statement that never
    mentions `R`. SFC holds wherever `CR` is elementary, and fails only under SFG, which itself implies amenability.
  - *New route structure for the root (new nodes).* RGAP₁ is now a claim node,
    `thompson-f-ramsey-radius-single-gap-below-reiter-radius`, with the direct route
    `thompson-f-amenable-via-single-ramsey-reiter-gap`. It has two routes, one per disjunct:
    `thompson-f-single-ramsey-reiter-gap-via-costly-amplification` (¬AMP) and
    `thompson-f-single-ramsey-reiter-gap-via-second-test-function-gap` (SFG, new open claim
    `thompson-f-second-test-function-costs-more-than-any-tower`). So for the root, RGAP₂ is not needed: RGAP₁ is
    weaker than ¬AMP and suffices. RGAP₂ remains relevant only as a route to ¬AMP itself.
  - *Not new, recorded to avoid repetition.*
    - Single-pair halving `PR_{c(c/2)^{k−1}}(m) ≤ PR_c^{∘k}(m)` is a composition-per-halving scheme like Towsner's.
      It gives nothing below a tower.
    - The Bhattacharyya bridge from an ℓ¹ pair balance to an ℓ² return gives only `⟨λ(τ)η, η⟩ ≳ 1/k` at the second
      step, far below the `1/2` that RRET needs.
  - *Remaining shape.* A refutation of RGAP₁ (CRE) kills ¬AMP, SFG and RGAP₂ at once. A proof of the root
    along this family needs either ¬AMP, a precision gap, or SFG, a multiplicity gap. Encoding two test functions as
    one is selector or marker coding, already killed above, so SFC has no known proof. A proof of SFG would need a
    pair `(α, β)`-uniform construction whose cost is visibly smaller than that of joint invariance under both
    generators. Neither was found.
