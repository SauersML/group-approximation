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
  - research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md
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

**Fold bootstrap: exact single-double-coset criterion, odometer actions and
iid seeds (September 18, 2026, swarm-0917-w7-w7-fp-follow, finite-models).**
Artifact `research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`.
Scripts in `experiments/fpbs-fold-bootstrap-2026-09-17/`.
- **Exact criterion.** At `K = <a, bab^{-2}> ≤ F_2`, for every free action,
  `E_K ∨ b|_A = E_L` iff the 2-of-3 closure of `A` on the triples
  `{w, aw, bw}` is conull. The proof is a Stallings fold of the coset hulls
  (artifact §1). So graphings using the double coset `K b K` alone achieve
  exactly `σ_b = inf { μ(A) : cl(A) conull }`.
- **Settled for odometer actions.** If the action has a factor
  `z ↦ z + χ(g)` on `Ẑ` with `χ(a) = 1`, then three residues mod `N` suffice,
  so `relC = 0` (Lemma 2.1). For `Gamma_mal` this gives
  [[fpbs-mal-odometer-product-actions-have-cost-two]]: `β × Ẑ_χ` has cost 2
  for every free `β`, and `C(Gamma_mal) = 2`.
- **Bernoulli bound.** For iid single-site seeds the closure is conull iff
  `p > 5/32`. The triple complex is a hypertree, the recursion is
  `y = p + (1−p)(2y^2 − y^4)`, and it is tangent at `y = 1/3`. So Bernoulli
  has `relC ≤ 5/32`, and `5/32` is the exact single-site sprinkling
  threshold. It is not `0`, and a bound per stage does not telescope to a
  finite cost.
- **Where it dies for Bernoulli.** The Bernoulli shift is mixing, so it has no
  compact factor, and the odometer seeds are not available. Nonabelian finite
  quotients give only `r(Q)/|Q| ≈ 0.10` (best `848/8192`, Zassenhaus
  `(2,4)`). No lower bound on `σ_b` is known. The BLPS mass-transport bound
  for 2-neighbour bootstrap fails because core-free complements can be
  many-ended.
- **Remaining case.** The claim is now open exactly for free actions without
  such a factor, Bernoulli first. There, `relC = 0` needs either
  factor-of-iid seed sets with conull closure and density tending to `0`
  (iid single-site seeds need more than `5/32`), or labels outside
  `K b^{±1} K`.

**Amenable bridges (September 18, 2026, swarm-0917-w9-w9-fp-last1,
probability-random).** Node `fpbs-malnormal-cosets-admit-no-amenable-bridges`,
ESTABLISHED.
- Tried: get `relC(E_L ; E_K) = 0` from an amenable `E ⊆ E_L` with
  `E ∩ E_K` aperiodic and `E_K ∨ E = E_L`, via
  `relC(E_L ; E_K) ≤ relC(E ; E ∩ E_K)`. This is the amenable-subrelation
  extension of infinite-contact repair.
- Where it dies: for malnormal `K` and every free action, such an `E` lies in
  `E_K`. An `E`-invariant field of boundary measures on the orbit trees must
  be carried by the limit set of each infinite `E ∩ E_K`-piece; this is a mass
  transport to the heaviest hull vertices. Distinct `K`-cosets have disjoint
  limit sets. So each `E`-class meets at most one coset in infinite pieces.
- What survives: amenable `E` whose trace on `E_K` has large finite classes
  (approximate bridges, of small positive relative cost), and non-amenable
  bridges such as the fold graphings `b|_A`.

