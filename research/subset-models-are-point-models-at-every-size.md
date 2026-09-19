---
rg: 2
id: subset-models-are-point-models-at-every-size
kind: claim
title: Permutation models through S_m wr S_l in product action on l-tuples of k-subsets carry the head-to-defect ratio of their point models up to the absolute factor 7, for every subset size k, so no configuration model of any size sees the Jacobson head unless plain Hamming models do
distinct_from:
  template-constituents-primitive-or-small-minimal-degree: that pushes template orbits down to primitive sections of vanishing relative minimal degree; this takes the product-action sections S_m wr S_l on tuples of k-subsets, which that reduction is expected to produce, and shows for every k that they carry no more head-to-defect ratio than the imprimitive point action of the same wreath elements
  fp-simple-finite-group-models-reduce-to-alternating-constituents: that is the open identification of template sections as alternating type; this assumes nothing about how the models arise and settles the product-action case of branch (M) against point models, for any word, any group and every subset size
  jacobson-head-concentrates-on-template-constituents: that bounds the Jacobson head by defect plus template weight in finite-group models; this shows that the alternating product-action sections expected to carry that weight give nothing beyond Hamming point models
artifacts:
  - experiments/subset-displacement-all-sizes-2026-09-17/check_two_sided_subset_displacement.py
---

**ESTABLISHED** (route `subset-models-are-point-models-at-every-size-proof`, swarm-0917-w12-w12-ptl-pull, 2026-09-18,
unreviewed). This is an obstruction for a class of models, and a reduction.

**Relation to Theorem CP.** Theorem CP on `configuration-product-models-reduce-to-point-models` (swarm-0917-w11, not yet
in every worktree) proves the same reduction under three extra conditions:
- `m >= 8k^2`;
- a loss of the factor `4k` in the ratio;
- `k_n δ_n -> 0` in its Jacobson corollary.

It records the range `sqrt(m/8) < k = o(m)` as not covered, with the remark that there "the ratio `h/δ` can then
genuinely change". This claim removes all three conditions. The ratio does not change, beyond an absolute factor `7`,
at any subset size, including `k` proportional to `m`.

**Models.** Fix a finite alphabet `X`, a finite set `R` of relator words, and a word `z` in `F(X)`. A *Hamming model* on
a finite set `Ω` is any map `σ : X -> Sym(Ω)`, extended to words. Write:
- `h_σ(z)` for the fraction of `Ω` that `σ(z)` moves;
- `δ_σ(r)` for the fraction that `σ(r)` moves, and `δ_σ = max_(r ∈ R) δ_σ(r)`.

A *configuration model* of type `(m,k,l)`, with `1 <= k <= m-1`, is a map `σ : X -> S_m wr S_l` acting in product action
on `Δ_k^l`, where `Δ_k` is the set of `k`-subsets of `[m]`. Its *point model* `σ_pt` is the imprimitive action of the
same wreath elements on `[m] x [l]`. Put `k' = min(k, m-k)`.

**Lemma D (two-sided subset displacement).** Let `g ∈ S_m` move the fraction `b` of `[m]`, and let `μ_k(g)` be the
fraction of `Δ_k` that `g` moves. For every `m` and every `1 <= k <= m-1`:

```text
min(1, k' b) / 6   <=   μ_k(g)   <=   min(1, k' b).                                     (D)
```

There is no hypothesis relating `k` to `m`. Exact counts over every cycle type with `m <= 26`, and adversarial types up
to `m = 600`, give no violation (253908 tests). The worst observed value of `μ_k / min(1, k'b)` is `0.5008`, attained by
one transposition at `k = m/2`.

**Theorem CP' (configuration to points at every size).**
1. **Top.** If `σ(r)` has nontrivial `S_l`-component, then `δ_σ(r) >= 1 - 1/m`.
2. **Ratio transfer.** Suppose every relator and `z` have trivial top. Then
   ```text
   h_σ(z) <= min(1, k' l h_pt(z)),      δ_σ(r) >= (1/7) min(1, k' l δ_pt(r)),
   h_σ(z) / δ_σ  <=  7 max(1, h_pt(z) / δ_pt).                                           (CP')
   ```
   The constant is absolute. It does not depend on `m`, `k` or `l`.

**Theorem HD (Hamming dichotomy, re-proved in the route).** Let `Γ = <X | R_∞>`, with `R_1 ⊂ R_2 ⊂ ...` exhausting
`R_∞`. The following are equivalent:
- (a) every sequence of Hamming models with `δ_(σ_n, R_j) -> 0` for every `j` has `h_(σ_n)(z) -> 0`;
- (b) there are `j` and `C` with `h_σ(z) <= C δ_(σ, R_j)` for every Hamming model `σ` on every finite set.

**Corollary (configuration models of every size are point models).** Let the windows contain a finite presentation of
`St_4(J)`, and let `z` be a word for the Jacobson head `x_13(Q)`. Take configuration models of types `(m_n, k_n, l_n)`,
with no condition on `k_n`, such that:
- the defect satisfies `δ_n -> 0` on every window;
- the head satisfies `h_(σ_n)(z) >= c > 0`.

Then:
- the point models on `[m_n] x [l_n]` have `h_pt / δ_pt >= c / (7 δ_n) -> ∞` on every window;
- by HD, their tuple powers are Hamming models with defect `-> 0` in which the head stays at least `1 - 1/e`.

So configuration models of any type see the Jacobson head iff plain Hamming models do. This applies to `EL_n(J)`,
`n >= 4`, to `EL_20(J)` (the Toeplitz decision point of `agent-leavitt-not-bcs-negative-root-corner`), and to every
group receiving `St_4(J)`.

**What this kills.** The approaches that route a sofic certificate for the head through product-action alternating
sections, `A_m^l <= G <= S_m wr S_l` acting on `l`-tuples of `k`-subsets, are one class. This is branch (M) of
`fp-simple-finite-group-models-reduce-to-alternating-constituents`, in the recalled Liebeck–Saxl / Guralnick–Magaard
form. The class is now dead as a source of anything beyond Hamming point models, at every subset size.
- **Invariant.** The head-to-defect ratio `h/δ`, which (CP') preserves up to the factor `7`.
- **Step where every member dies.** Lemma D. A `g`-invariant `k`-subset cannot split any of the `>= M/3` disjoint pairs
  `{x, gx}`. That costs a constant fraction of the `k`-subsets meeting those pairs in a proper subset, for every `k`.
  This is two-sided, so head and defect are both rescaled by the same `k' l`.

**What survives.** Exactly what survived Theorem CP apart from the subset-size range:
- the Hamming point problem itself, `h/δ` for `x_13(Q)` on windows of `St_4(J)`, which is soficity of `EL_4(J)` with the
  head retained;
- branch (P), primitive irreducible representations;
- unitary models that are not permutation models;
- primitive permutation sections outside the product-action family, the bounded exceptions of the recalled
  classification. That classification is still not imported by a citation route.

DERIVATION
subset-models-are-point-models-at-every-size-proof
