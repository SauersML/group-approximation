---
rg: 2
id: fpbs-profinite-relcost-equals-relative-rank-gradient
kind: claim
title: On a free profinite action of F_2, the relative cost over K = <a, bab^-2> is the relative rank gradient of the point stabilizers, and a positive relative rank gradient along one free tower gives the Bernoulli promotion floor Q_0 > 0
distinct_from:
  fpbs-abert-nikolov-rank-gradient-equals-profinite-cost: that is the absolute statement, cost minus one equals the rank gradient; this is its relative version over a subgroup K, where the rank count is useless because Stab_K(q) and Stab_L(q) both have rank |Q|+1.
  fpbs-mal-floor-iff-deep-promotion-floor: that reduces the Bernoulli floor to Q_0 > 0 together with a uniform depth condition; this turns Q_0 > 0 into a finite combinatorial lower bound on relative ranks along a tower of finite quotients, and decides neither.
  fpbs-relative-fixed-price-free-pairs: that claims relC = 0 for every free action; this shows that claim forces the relative rank rk(Stab_L(q) : Stab_K(q)) to be o(|Q|) along every free tower of finite L-sets.
artifacts:
  - research/artifacts/fpbs-relative-rank-collapse-2026-09-18.md
  - experiments/fpbs-relative-rank-collapse-2026-09-17/fold.py
  - experiments/fpbs-relative-rank-collapse-2026-09-17/greedy.py
  - experiments/fpbs-relative-rank-collapse-2026-09-17/checks.py
  - experiments/fpbs-relative-rank-collapse-2026-09-17/checks_out.txt
  - experiments/fpbs-relative-rank-collapse-2026-09-17/greedy_out.txt
  - experiments/fpbs-relative-rank-collapse-2026-09-17/fold_out.txt
---

**ESTABLISHED** through `fpbs-profinite-relcost-equals-relative-rank-gradient-proof`.

**Setting.** Let `L = F(a, b)` and `K = <a, c>` with `c = b a b^{-2}`. Let `L` act
on the right on a finite set `Q`. A *chord* is a pair `(p, w)` with `p ∈ Q` and
`w ∈ L`. On any action `X` with an equivariant map `π : X → Q`, it acts as the
partial map `x ↦ x·w` on `π^{-1}(p)`. Let `d(Q)` be the least number of chords
that, together with `E_K`, generate `E_L` on every free action with factor `Q`.
Write `relC(X) = relC(E_{X|L} ; E_{X|K})`.

**(1) Folding criterion.** A set of chords works iff Stallings folding of the
labelled graph below, taken over `Q`, has exactly `|Q|` vertices. The graph has
real vertices `Q`, an `a`-edge `p → p·a`, a `c`-path at every `p`, and a path
labelled `w` from `p` to `p·w` for each chord.

**(2) Relative rank.** If `K` is transitive on `Q`, then
`d(Q) = rk( Stab_L(q) : Stab_K(q) )`. This is the least number of elements that
must be added to `Stab_K(q)` to generate `Stab_L(q)`. The group
`Stab_K(q) = K ∩ Stab_L(q)` is malnormal in `Stab_L(q)`, and both groups are
free of rank `|Q| + 1`.

**(3) Profinite identity.** Suppose `X = lim Q_m` is an essentially free
profinite action of `L`, with Haar measure. Then

```text
relC(X) = lim_m d(Q_m)/|Q_m| = inf_m d(Q_m)/|Q_m| .
```

The bound `relC(X) ≤ d(Q)/|Q|` holds for every action `X`, free or not, that
has `Q` as a factor.

**(4) Consequence for the floor.** Let `ρ` be the Bernoulli shift of `L`, and
let `Q_0 = relC(ρ)` be as in `fpbs-mal-floor-iff-deep-promotion-floor`. Then
`Q_0 ≥ inf_m d(Q_m)/|Q_m|` for every free tower `(Q_m)`. So a linear lower
bound on the relative rank along a single free tower proves `Q_0 > 0`, which
refutes `fpbs-relative-fixed-price-free-pairs` at Bernoulli. Conversely, that
claim predicts `d(Q_m) = o(|Q_m|)` along every free tower, and a finite
computation can test that prediction.

**Evidence, not proof.**
- Greedy merge search gives upper bounds `d/n ≈ 0.108–0.12` on random `Q`, at
  `n = 200` and `n = 600`.
- Random single merges need `≈ 0.155 n` chords, in line with the iid threshold
  `5/32`.
- Odometers `Z/N` with `b ↦ +k` stay bounded (`d ≤ k`), consistent with
  `fpbs-mal-odometer-product-actions-have-cost-two`.
- An exhaustive test finds no single chord that works on any transitive random
  `Q` with `8 ≤ n ≤ 80`.
- None of these is a lower bound. See the artifact.
