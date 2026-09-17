---
rg: 2
id: fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction
kind: claim
title: A fixed-price counterexample among f.g.-by-cyclic groups via profinite actions reduces to inner-type chains, and positive profinite gradient suffices
distinct_from:
  fpbs-quotient-split-actions-have-cost-one: that gives the cost-one side (Theorem A); this locates where the other side, a free action of cost greater than one, can come from for f.g.-by-cyclic groups.
  fpbs-bounded-cost-outer-cyclic-extension-price-one: that concerns fixed price one for bounded-cost-by-cyclic extensions; this is a structure theorem for Farber chains of positive rank gradient in the same groups and a profinite sufficient criterion.
  fpbs-kazhdan-rankgradient-counterexample-reduction: that route needs a Kazhdan group with positive rank gradient and cost one; this uses f.g.-by-cyclic groups, whose infimal cost 1 is proved in-repo, and moves the difficulty into a profinite embedding problem.
artifacts:
  - research/fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction-proof.md
  - experiments/mapping-torus-inner-quotients-2026-09-17/inner2.g
  - experiments/mapping-torus-inner-quotients-2026-09-17/run2.out
---

**ESTABLISHED (reduction, sufficiency direction plus necessity of type).**
Proofs are in `research/fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction-proof.md`.

Let `Gamma = N x|_phi Z` with `N` f.g. infinite, and let `(Gamma_n)` be a Farber
chain (normal, descending, trivial intersection). Put
`k_n = [Gamma : Gamma_n N]`.

1. **Unbounded type is dead.** If `k_n -> infinity`, then `RG(Gamma,(Gamma_n)) = 0`.
   The bound is `(d(Gamma_n)-1)/[Gamma:Gamma_n] <= (d(N)-1)/k_n + 1/[Gamma:Gamma_n]`.
2. **Bounded type is inner type.** If `k_n` is bounded, then after replacing
   `phi` by `phi^k`, the subgroup `N` surjects onto every `Gamma/Gamma_n`.
   Moreover `X = lim Gamma/Gamma_n` carries data (D):
   - an injective `iota : N -> X` with dense image;
   - `g` in `X` with `iota(phi x) = g iota(x) g^-1`;
   - `g^j` not in `iota(N)` for `j != 0`.

   In addition `RG(Gamma) >= RG(X)`.
3. **Criterion (converse construction).** Any data (D) for `(N, psi, X)` and
   any chain `U_n` of open normal subgroups with trivial intersection give:
   - an injective dense `Gamma = N x|_psi Z -> X`;
   - an inner-type Farber chain `Gamma_n` with `RG(Gamma,(Gamma_n)) >= RG(X,(U_n))`.
4. **Counterexample.** If moreover `RG(X,(U_n)) > 0`, then `Gamma` has two free
   p.m.p. actions of different costs:
   - the Abért–Nikolov profinite action, of cost `1 + RG > 1`;
   - `beta x` (irrational rotation), of cost 1 by `fpbs-quotient-split-actions-have-cost-one`.

   The same holds for any dense f.g. `Gamma <= X` of infimal cost 1.
5. **Obstructions.**
   - If `X` has an infinite topologically f.g. abelian closed normal subgroup,
     then `RG(X) = 0`.
   - Hence monodromy of finite order in `Out(N)` gives nothing. This is the
     calibration case `N x Z`, which has fixed price 1.
   - Finite-rank completions (p-adic analytic, single-prime congruence) give nothing.
   - In `X = F^_p(2)`, the discrete free subgroup on a basis admits no (D).
     This uses p-conjugacy separability together with Grossman's theorem.

**Why this is new relative to dead routes.** The Kazhdan routes need a
positive-gradient group that is also cost-one, and they stall on proving the
cost side. Here the cost-one side is proved (Theorem A), and all remaining
difficulty is concentrated in one profinite embedding problem. That problem is
target P: a positive-gradient profinite group, e.g. `F^_p(2)` on its p-power
chains, containing a dense copy of `N` normalized modulo `iota(N)` by an element
of infinite order outside `iota(N)`, with infinite-order outer monodromy.

**Scope.**
- Not proved: that the discrete gradient being positive forces the profinite
  gradient to be positive. So 3–4 give sufficiency only.
- Not proved: target P.
- Proving `RG = 0` for all inner-type chains would settle the known-open
  vanishing of rank gradient for fibered hyperbolic 3-manifold groups.
- First falsifiable step: exhibit (D) inside `F^_p(2)` for `N` a non-standard
  dense f.g. subgroup, or prove that every (D) in a free pro-p group forces a
  central element.

**Computation (exploratory, rules out nothing global).**
`experiments/mapping-torus-inner-quotients-2026-09-17/` enumerates inner-type
levels `Gamma -> PSL_2(q)`, `q <= 13`, of the figure-eight mapping torus
(`a -> ab`, `b -> bab`). It reports `d_2`, `d_3` and `b_1` of the kernels.

- There is no inner-type level for `q = 5, 11`.
- Levels exist for `q = 7, 8, 9, 13`, with `(d_p-1)/|G|` between 0.089 and 0.244.
- `d_p` exceeds `b_1` by at most 1.
- Calibration: the untwisted case `F_2 x Z` gives ratio about 1 at levels
  where `t` maps trivially. These are single levels; by 4.2 the gradient of any
  inner-type chain in `F_2 x Z` is 0, so a high ratio at a finite level carries
  no information on its own.

The ratios are upper bounds for the mod-p gradient of p-power refinements
through each level. By Lück approximation `b_1/index -> 0`, so any positive
gradient must come from mod-p torsion in deeper levels, not from `b_1`.

## Attempts

- 2026-09-17 sw-116: p-deficiency certificates fail. Mapping tori have
  `def_p <= 1`, and the Zassenhaus-depth bound does not beat calibration on `Z^2`.
- 2026-09-17 sw-116: finite-rank completions of arithmetic fibered groups are
  killed by 4.3.
- 2026-09-17 sw-116: literature checked. 2305.10410 covers only polynomially
  growing monodromy, 2402.14130 needs chains with trivial pro-p intersection,
  and Garrido–Klopsch 1901.03101 does not obstruct P.
