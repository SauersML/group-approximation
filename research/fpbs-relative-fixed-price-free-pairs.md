---
rg: 2
id: fpbs-relative-fixed-price-free-pairs
kind: claim
title: For a free action of a finitely generated free group, the relative cost over a nontrivial finitely generated subgroup is at most the positive part of the rank difference
distinct_from:
  fpbs-relative-fixed-price-fg-pairs: that is the general finitely generated pair statement; this is its free-pair case, which by Gaboriau's fixed price for free groups is stated with ranks and unconditionally implies finite cost for locally free groups.
  fpbs-mal-bernoulli-single-stage-floor: that conjectures a positive floor at the pair (F_2, <a, bab^-2>) for one action; this claim implies the floor fails.
  fpbs-locally-free-malnormally-exhausted-finite-cost: that is the open finite-cost statement for the malnormally exhausted case of locally free groups; this is a finitely generated pair inequality that implies finite cost for every locally free group with finite c*.
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

**OPEN.** Let `K ≤ L` be nontrivial finitely generated free groups, and let
`a` be a free p.m.p. action of `L`. Prove

```text
relC( E_{a|L} ; E_{a|K} ) ≤ ( rk L − rk K )^+ .
```

By Gaboriau's lecture notes Cor 2.25 ("The following groups are strongly
treeable and have fixed price: C∗(Fn) = C∗(Fn) = n for the free group of rank
n."), the costs are the ranks. So this is the free-pair case of
`fpbs-relative-fixed-price-fg-pairs`.

**Content.** The claim is trivial or known for:
- normal and commensurated `K`;
- finite-index `K`;
- free factors;
- `K` cyclic.

The open case is `K` malnormal with `rk K ≥ rk L`, for instance
`K = <a, bab^{-2}> ≤ F_2`. There the claim asks for `relC = 0`.

**Why it matters.** By the route
`fpbs-locally-free-finite-cost-from-relative-free-pairs`, it gives
`fpbs-locally-free-free-actions-have-finite-cost`, and hence fixed price
`c* = 1 + β_1^(2)` for every countable locally free group. This does not
assume fixed price for finitely generated groups.

**Minimal test.** At `L = H_2 = <a, b_2>`, `K = H_1 = <a, b_1>` inside
`Γ_mal`, with `a` the Bernoulli shift of `Γ_mal` restricted to `H_2`, this
claim gives `C(β) = 2`. So it refutes `fpbs-mal-bernoulli-single-stage-floor`.
Conversely, that floor refutes this claim (artifact §3.2, Proposition 3).

## Attempts

**Where the obvious attacks die (September 17, 2026; artifact §2.2 and §4).**
- **Packing repairs over a malnormal `K`.** These die on the ESTABLISHED
  finite-contact and linear-perimeter floors. Every bounded-detour packing
  certificate has a positive floor, so `relC = 0` would need unbounded labels.
- **Infinite-contact repair** (`fpbs-infinite-contact-zero-relative-cost`).
  Its hypothesis fails exactly for malnormal `K`.
- **Relative L2 and rank-gradient bounds.** They vanish, so they separate
  nothing.
