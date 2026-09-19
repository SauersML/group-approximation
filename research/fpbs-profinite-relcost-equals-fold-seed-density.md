---
rg: 2
id: fpbs-profinite-relcost-equals-fold-seed-density
kind: claim
title: On an essentially free profinite action of F(a,b) with transitive levels, the relative cost over K = <a, bab^-2> equals the 2-of-3 fold seed density, so the Sanov 3-adic action forces the Bernoulli promotion floor Q_0 > 0 and relative fixed price fails for free pairs
distinct_from:
  fpbs-mal-profinite-fold-density-is-finite-percolation: that computes sigma_b of a profinite action as lim r(Q_n)/|Q_n| and bounds Q_j above by sigma_b; this proves the matching lower bound relC >= sigma_b over graphings with arbitrary labels, so on profinite actions the single-double-coset cost is the whole relative cost.
  fpbs-strongly-ergodic-actions-have-fold-seed-floor: that bounds only sigma_b, which is the cost of graphings with labels in one double coset K b K; this shows that on profinite actions no graphing with any labels beats sigma_b, which turns that floor into a relative-cost floor.
  fpbs-mal-bernoulli-single-stage-floor: that is the open target, equivalent to inf_j Q_j > 0; this proves only its depth-0 half (D0), Q_0 > 0, and leaves the depth-uniformity half (D1) open.
  fpbs-relative-fixed-price-free-pairs: that claims relC = 0 at every free action of the pair (F_2, <a, bab^-2>); this gives free actions, profinite and Bernoulli, where relC > 0, so it refutes that claim.
  fpbs-mal-promotion-cost-monotone-under-weak-containment: that reduces lower bounds for Q_j to some free witness at each depth and proves no bound; this supplies the depth-0 witness with an exact value.
  fpbs-word-chords-are-dominated-by-merges: that is the finite-level identity d(Q) = r(Q) for chords with arbitrary labels; this is its profinite consequence together with the clopen approximation that passes from graphings to chords.
artifacts:
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/sanov_gap.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/sanov_gap_out.txt
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/rho_vs_r_out.txt
---

**ESTABLISHED** through `fpbs-profinite-relcost-equals-fold-seed-density-proof`.

**Setting.**
- `L = F(a, b)`, `K = <a, c>` with `c = b a b^{-2}`, and `φ(b) = c`, so
  `K = φ(L) = L_1`.
- For a p.m.p. action `X` of `L`, `relC(X) = relC(E_{X|L} ; E_{X|K})` is the
  infimum of the costs of graphings `Φ`, with labels anywhere in `L`, such that
  `E_{X|K} ∨ Φ = E_{X|L}`. This is `Q_0(X)` in the notation of
  [[fpbs-mal-promotion-cost-monotone-under-weak-containment]].
- `σ_b(X)` is the 2-of-3 fold seed density on the triples `(y, a y, b y)`, as
  in [[fpbs-mal-profinite-fold-density-is-finite-percolation]] and
  [[fpbs-strongly-ergodic-actions-have-fold-seed-floor]].
- A *profinite action* is `X = lim_n Q_n` along finite transitive `L`-sets
  with equivariant surjections `Q_{n+1} → Q_n`, with the inverse-limit
  measure.

**Claim.**

1. **(Identity.)** For every essentially free profinite action `X` of `L`,

   ```text
   relC(X)  =  σ_b(X)  =  inf_n r(Q_n)/|Q_n| .
   ```

   No graphing with labels anywhere in `L` does better than seeds of the
   single label `b`.

2. **(D0.)** Let `ρ` be the Bernoulli shift of `L`, and let `Q_0 = relC(ρ)` as
   in [[fpbs-mal-floor-iff-deep-promotion-floor]]. Then

   ```text
   Q_0  ≥  sup { σ_b(X) : X essentially free profinite }  >  0 .
   ```

   A witness is the Sanov 3-adic action. `L` acts on `SL_2(Z_3)` by right
   multiplication through `a ↦ [[1,2],[0,1]]` and `b ↦ [[1,0],[2,1]]`, with
   levels `SL_2(Z/3^k)`. It is free and profinite with transitive levels, and
   its levels form an expander family. By Theorem S,

   ```text
   Q_0  ≥  relC(Sanov_3)  =  σ_b(Sanov_3)  ≥  (1 − sup_k λ_2(SL_2(Z/3^k)))/4  >  0 .
   ```

   The w11 census gives `σ_b(Sanov_3) ≤ 1910/17496 < 0.1092`, so
   `relC(Sanov_3)` lies in `(0, 0.1092)`.

3. **(Relative fixed price fails for free pairs.)** The pair `K ≤ L` has
   `rk K = rk L = 2`. The Bernoulli shift `ρ` and the Sanov action are free
   actions of `L` with `relC > 0 = (rk L − rk K)^+`. So
   [[fpbs-relative-fixed-price-free-pairs]] is false. By Gaboriau's fixed price
   for free groups, `C(E_{X|L}) = C(E_{X|K}) = 2`, so the free-pair case of
   [[fpbs-relative-fixed-price-fg-pairs]] fails at the same actions.

4. **(Conditional sharpening.)** If some essentially free profinite `X` is
   weakly contained in `ρ`, then
   [[fpbs-bernoulli-fold-seeds-have-density-at-least-2-25]] gives
   `Q_0 ≥ σ_b(X) ≥ 2/25`. No such `X` is known.

**What this leaves.** [[fpbs-mal-bernoulli-single-stage-floor]] is
equivalent to `inf_j Q_j(ρ) > 0`. This claim proves the `j = 0` term is
positive (D0). Depth uniformity (D1) is not touched: at depth `j` the labels
lie in `L`, not in `L_j`, and the chords may reach `t_j = φ^j(b)` through
parts of the folded graph that contain no vertex of the base graph (see the
route, §5).

**Evidence.**
- `sanov_gap.py` gives `λ_2 = 0.6830, 0.7938, 0.8687` for `k = 1, 2, 3`. The
  script also checks that the levels are transitive. These values are
  evidence only. The proof uses the uniform gap of Selberg and
  Bourgain–Gamburd, whose constant is not explicit here.
- `rho_vs_r_out.txt` records the finite identity `ρ(Q) = r(Q)` on 48 random
  levels.
