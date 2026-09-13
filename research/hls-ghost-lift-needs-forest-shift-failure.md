---
rg: 2
id: hls-ghost-lift-needs-forest-shift-failure
kind: claim
title: Under max-to-reduced K_0 injectivity at the tree boundary, a full-shift class with ghost ranks on marked expanders refutes the Bernoulli comparison and Baum--Connes surjectivity at the forest shift
distinct_from:
  hls-ghost-projection-breaks-k-exactness: that is HLS's non-exactness for l^inf(N; c_0(G)); this transports it to the Bernoulli full shift and shows what a lift of the HLS class forces.
  bernoulli-pattern-expansions-are-finite: that proves ranks are local on every host; this uses locality to show that ghost ranks on expanders come with a non-cylinder class on the forest shift.
---

**ESTABLISHED** by `hls-ghost-lift-needs-forest-shift-failure-proof` (unreviewed). Full proofs:
`research/artifacts/bc-bernoulli-hls-ghost-lift-2026-09-13.md`.

**Hypotheses (M).**
- `G` is torsion-free with finite symmetric generating set `S`.
- `X_n` are connected `D`-regular graphs, with `D >= 3`, spectral gap `ε`, girth tending to infinity and strictly
  increasing sizes.
- `A_n ⊆ G` are isometric images of the `X_n` with `d(A_n, A_m) -> ∞`, as in Osajda's groups; torsion-freeness is assumed.

**Objects.**
- The marked configurations are `x_n = 1_(A_n) ∈ X = (Z/p)^G`, and `Ŷ = closure(∪_n G·x_n)`.
- The **tree boundary** is `∂Y = Ŷ \ ∪_n G·x_n`. Its nonzero points are `D`-regular tree configurations.
- The **forest shift** is `T = {x : supp x induces a forest in Cay(G, S)}`. Then `T ⊇ ∂Y`, and `T_r^T` is its
  cylinder comparison.
- The HLS projection `p ∈ C_0(Ŷ \ {0}) ⋊_r G` is the kernel projection of the induced Laplacian plus the identity off the
  support. It has `r_(x_n)[p] = 1` and dies on `∂Y` (`hls-ghost-projection-breaks-k-exactness`, Section 7).

**(H-K)** `K_0(C_0(∂Y \ {0}) ⋊_max G) -> K_0(C_0(∂Y \ {0}) ⋊_r G)` is injective. This is the hypothesis of HLS Lemma 1(2).

**Theorem.** Assume (M) and (H-K). Let `y ∈ K_0(C_0(X \ {0}) ⋊_r G)` have `y|_(∂Y) = 0` and `r_(x_n)(y) ≠ 0` for
infinitely many `n`. Then:
1. `y ∉ im T_r`. So the Bernoulli cylinder comparison fails to be surjective, and reduced assembly for `F_p wr_G G` fails
   to be surjective.
2. `y - T_r(n(y))` is a nonzero rank-invisible class (shape (b)).
3. `y|_T ∉ im T_r^T`. So Baum--Connes surjectivity fails for `G` with coefficients `C_0(T \ {0})`; by weak K-equivalence
   and going-down, `T_r^T` is this assembly map.

**Corollary.**
- `[p]` is not a combination of cylinder classes on `Ŷ`.
- Any lift of `[p]` along `C_0(X \ {0}) ⋊_r G -> C_0(Ŷ \ {0}) ⋊_r G` satisfies 1--3.
- If Baum--Connes surjectivity holds at `C_0(T \ {0})`, the HLS class does not lift.

**Key step.** Assume (H-K). If `m` is a finitely supported cylinder combination with zero restriction to `∂Y`, then its
counts on `A_n` vanish for large `n`.
- Lift the combination to the maximal crossed product. Its boundary part vanishes there, by (H-K).
- The maximal sequence `0 -> c_0(N×G) ⋊ G -> C_0(Ŷ \ {0}) ⋊_max G -> C_0(∂Y \ {0}) ⋊_max G -> 0` is exact. So the
  combination comes from `⊕_n Z`.
- Its ranks at `x_n` are therefore eventually `0`.
- Locality (`bernoulli-pattern-expansions-are-finite`) makes the ranks of `y` at `x_n` and at finite forests counts of
  the same forest patterns.

**Doors.**
- The Haar trace is blind to this route, since `μ(T) = μ(Ŷ) = 0`.
- `K_1` is not forced.
- Given (H-K), the expander route has become a question about forest configurations.

**Model tests.**
- For `y = [1_(C_s)]` with `s` one site, the ranks at `x_n` are `|A_n| ≠ 0`, but `y|_(∂Y) ≠ 0`. The hypothesis fails, as
  it must for a cylinder class.
- `[p]` itself has boundary `0` and ranks `1`, but lives on `Ŷ`. The corollary says it is not a cylinder combination
  there, which matches HLS's "does not come from `c_0(N × G)`".
