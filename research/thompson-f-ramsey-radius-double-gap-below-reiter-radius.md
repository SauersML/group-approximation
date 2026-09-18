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
