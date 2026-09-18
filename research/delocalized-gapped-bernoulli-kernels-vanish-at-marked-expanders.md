---
rg: 2
id: delocalized-gapped-bernoulli-kernels-vanish-at-marked-expanders
kind: claim
title: Over hosts with embedded large-girth expanders, a gapped full-shift Bernoulli operator whose kernel delocalizes along the marked expanders is eventually invertible there, so expander-cluster gap labels give no trace defect
distinct_from:
  hls-ghost-class-never-lifts-to-the-bernoulli-full-shift: that is the K-theoretic statement about classes vanishing on the tree boundary; this turns spectral delocalization of a gapped operator into that boundary vanishing, and uses it to kill the Haar-trace expander-cluster recipe.
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that supplies the trace detector Z[1/p] for F_p wr_G G; this shows that its natural expander-cluster instance, trace sum_n p^(-|N_n|), is realized by no gapped operator.
  bernoulli-pattern-expansions-are-finite: that shows gapped operators have local ranks over finite-support configurations; this concerns delocalized kernels at the marked expanders and their boundary limits, and needs the CND restriction theorem, not locality alone.
  monster-bc-failure-at-measured-coefficient-is-the-module-crux: that asks for any non-tracial detector at a measured coefficient; this closes one tracial construction at the Bernoulli coefficient and names the property a surviving witness must have.
---

**ESTABLISHED** by `gapped-bernoulli-kernels-vanish-via-boundary-continuity` (unreviewed). This is a
corollary-level obstruction built on Theorem D (`hls-ghost-class-never-lifts-to-the-bernoulli-full-shift`), which is
itself unreviewed.

**Setting.**
- `G` is finitely generated and torsion-free and satisfies hypotheses (M) of `hls-ghost-lift-needs-forest-shift-failure`:
  - isometrically embedded `D`-regular expanders `A_n ⊆ G` with `D >= 3`;
  - girth tending to infinity;
  - strictly increasing sizes;
  - `d(A_n, A_m) -> ∞`.
- `Λ` is a finite alphabet with `0 ∈ Λ` and `|Λ| >= 2`, `X = Λ^G` and `X^0 = X \ {0}`. The marked configurations are
  `x_n = 1_(A_n)`, `N_n = {v : d(v, A_n) <= 1}` and `∂Y = closure(∪_n G·x_n) \ ∪_n G·x_n`.
- `E : M_k(C(X) ⋊_r G) -> M_k(C(X))` is the canonical conditional expectation, and `π_z` is the regular representation
  at `z ∈ X`. The diagonal entries of `π_z(b)` are the values of `E(b)` along the orbit `G·z`.
- `a = a* ∈ M_k(C(X) ⋊_r G)` is **gapped**: `spec(a) ∩ (-δ, δ) ⊆ {0}` for some `δ > 0`. `P = 1_({0})(a)` is its kernel
  projection, which lies in the algebra by continuous functional calculus. Write `a_z = π_z(a)` and `P_z = π_z(P)`.

**Theorem K.** Assume (M), and let `a` be gapped with `a_0 = ev_0(a)` invertible.
- (a) **Boundary vanishing kills the kernel.** If `tr E(P)` vanishes on `∂Y \ {0}`, then `a_(x_n)` is invertible for all
  large `n`.
- (b) **Delocalization implies boundary vanishing.** If `sup_(w ∈ G·x_n) tr E(P)(w) -> 0`, then `tr E(P)` vanishes on
  `∂Y \ {0}`. Equivalently, `sup_h ⟨P_(x_n) δ_h, δ_h⟩ -> 0`.
- (c) **Forced localization.** Suppose `ker a_(x_n) ≠ 0` for every `n` in an infinite set `S`. Then:
  - there is `ε > 0` with `sup_h tr⟨P_(x_n) δ_h, δ_h⟩ >= ε` for all large `n ∈ S`;
  - `tr E(P)(z) >= ε` at some `z ∈ ∂Y \ {0}`, so `P` restricts to a nonzero projection over the tree boundary.

**Proposition R (the killed recipe).** Take `Λ = Z/p`. Suppose a gapped `a` with `a_0` invertible has, at every
configuration, kernel equal to the normalized constants on its isolated marked clusters. An isolated cluster is a
translate `gA_n` with `z|_(gN_n) = (g·x_n)|_(gN_n)`. Then:
- the Haar trace is `τ(P) = Σ_n p^(-|N_n|)`;
- after passing to a subsequence with `|N_(n+1)| >= |N_n| + 2`, this trace lies outside `Z[1/p]`;
- item 7 of `bernoulli-bc-splits-into-host-and-cylinder-comparison` would then refute reduced assembly for `F_p wr_G G`.

By Theorem K (b) and (a), no such `a` exists. Its kernel at `x_n` has diagonal `1/|A_n| -> 0` and rank `1`.

**Consequences.**
- **Dead: the expander-cluster gap-label trace defect.** The recipe is to transplant the HLS ghost Laplacian to the full
  shift and read a non-`Z[1/p]` Haar trace off the positive-measure set of isolated clusters. Any construction of this
  kind fails at the gap step. The failure does not depend on the operator chosen, so it is not a matter of a bad
  penalty term.
- **What a gapped witness must look like at the marked expanders.** Either its kernel at `x_n` is eventually zero, or
  its kernel has diagonal bounded below and is seen by the boundary `∂Y \ {0} ⊆ T_cnd`. There Baum--Connes holds
  (`cnd-support-shift-bc-and-k-amenability`), and ranks are local finite pattern combinations
  (`bernoulli-pattern-expansions-are-finite`).
- **Where a trace defect must live.**
  - `bernoulli-pattern-expansions-are-finite`, item 2, makes `n(y)` finite. So `τ(T_r(n(y))) ∈ Z[1/p]`, and a
    Haar-trace defect in the ideal part `C_0(X^0) ⋊_r G` needs a rank-invisible class, shape (b) of
    `bernoulli-assembly-injective-beyond-the-host`, with trace outside `Z[1/p]`.
  - Theorem K adds that isolated expander clusters cannot supply that trace through a gapped kernel.

**Why it holds.**
- `E(P)` is continuous on `X`.
- Every point of `∂Y \ {0}` is a limit of `g_i·x_(n_i)` with `n_i -> ∞` (Lemma 1.1 of the CND artifact). So
  delocalization forces `E(P) = 0` on the boundary.
- `E` is faithful, so the restriction of `P` to `∂Y` is zero. Invertibility of `a_0` puts `P` in the ideal
  `M_k(C_0(X^0) ⋊_r G)`.
- Theorem D then gives `rank P_(x_n) = r_(x_n)[P] = 0` for large `n`, and the gap turns zero kernel projection into
  invertibility.
- (c) applies (a) and (b) to subsequences of the expanders. (M) passes to subsequences, and so does Theorem D.

**Model tests (calibration).**
- **Over the HLS subshift the statement is false, as it must be.** On `Ŷ` the HLS ghost projection is the kernel of a
  gapped Laplacian (context, `hls-ghost-projection-breaks-k-exactness`). It has diagonal `1/|A_n|` on `G·x_n`, it
  vanishes on `∂Y`, and it has rank `1` at every `x_n`. The proof uses the full shift exactly once, through Theorem D.
  The HLS class itself shows that the analogue of Theorem D over `Ŷ` is false.
- **One-site cylinder.** `a = 1 - 1_(C_({e},1))` is gapped with `a_0 = 1`. Its kernel at `x_n` has rank `|A_n|` and
  diagonal `1`, localized and seen by the boundary, consistent with (c).
- **`G = Z` or free groups with a free basis.** (M) fails and the theorem is empty.

**Scope.**
- Torsion-free finitely generated hosts satisfying (M), finite alphabets, and a single gapped self-adjoint matrix over the
  full Bernoulli crossed product.
- It says nothing about rank-invisible classes, which have no kernel at `x_n`, nor about `K_1`. Those are shapes (b) and
  (c) of `bernoulli-assembly-injective-beyond-the-host`, and they stay open.
