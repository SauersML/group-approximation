---
rg: 2
id: fpbs-mal-twisted-level-seed-density-uniform-witness
kind: claim
title: There is c > 0 such that at every depth j some essentially free profinite action of F(a,b) with transitive levels has 2-of-3 seed density at least c on all its phi^j-twisted levels
distinct_from:
  fpbs-profinite-relcost-equals-fold-seed-density: that proves the depth-0 case with the Sanov 3-adic tower; this asks for witnesses at every depth with one constant.
  fpbs-mal-overfold-merges-never-help: that is the exchange input deep_j = law_j; this is the density input, a lower bound on law_j(Q_m)/|Q_m| = r(Q_m^(j))/|Q_m| uniform in j.
  fpbs-mal-promotion-cost-monotone-under-weak-containment: that reduces the floor to per-depth free witnesses for Q_j with arbitrary labels; this asks for witnesses only for the lawful (L_j-labelled) cost, which is a fold seed density.
  fpbs-strongly-ergodic-actions-have-fold-seed-floor: that bounds sigma_b below for one action by its spectral gap; this needs the bound for the twisted actions X^(j), whose generators a, t_j get longer with j.
artifacts:
  - experiments/fpbs-depth-overfolding-2026-09-17/law_by_depth.py
  - experiments/fpbs-depth-overfolding-2026-09-17/law_by_depth_n120.txt
---

**OPEN.** Notation is as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]]. `Q^{(j)}` is `Q`
with `b` acting as `t_j = φ^j(b)`, and `r` is the 2-of-3 percolation number.
Prove that there is `c > 0` such that, for every `j ≥ 1`, some essentially
free profinite action `X_j = lim Q_m` of `L` with transitive levels
satisfies

```text
r(Q_m^{(j)})  ≥  c · |Q_m|      for all m.
```

Equivalently, `Q_j^law(X_j) ≥ c`, by item 4 of
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]].

**Known.**
- `j = 0` holds with the Sanov 3-adic tower. See
  [[fpbs-profinite-relcost-equals-fold-seed-density]].
- `r(Q^{(j)})` is additive over the `L_j`-orbits of `Q`, since the 2-of-3
  triples `(y, y·a^{-1}, y·t_j^{-1})` stay inside `L_j`-orbits.
- `X^{(j)}` is a free action of `L`, since `φ` is injective. So the
  question is whether the twisted actions `X^{(j)}` of a fixed tower, or of
  towers chosen depending on `j`, keep a uniform seed density.

**Routes that can fail.**
- **Fixed tower, uniform gap.** Take the Sanov 3-adic tower for every `j`.
  Theorem S of [[fpbs-strongly-ergodic-actions-have-fold-seed-floor]]
  bounds `σ_b(X^{(j)})` below in terms of the spectral gap of the generators
  `a, t_j` on the levels.
  - It needs a gap uniform in `j`. The word length of `t_j` grows
    exponentially (`|t_1| = 4`, `|t_2| = 11`), and nothing here controls the gap of `<a, t_j>` uniformly.
  - The gap for each fixed `j` would follow from strong approximation and
    Bourgain–Varjú. That is not written up here, and it is not uniform.
- **Towers adapted to `j`.** By M. Hall's theorem, `L_j` is a free factor of
  some finite-index `H_j ≤ L`. Inducing a good `L_j`-tower through `H_j`
  controls only the base `L_j`-orbit. That gives density at least
  `c_0 / [L : H_j]`, which is not uniform.
- **Random levels.** `law_by_depth.py` computes greedy upper bounds for
  `r(Q^{(j)})/n` on random `Q` with `n = 120`. They stay between `0.117`
  and `0.125` for `j = 0..4`, in 3 trials, and `Q^{(j)}` stays transitive.
  They are upper bounds only, so they show no decay but prove nothing.
