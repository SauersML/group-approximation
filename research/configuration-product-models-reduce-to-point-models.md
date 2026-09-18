---
rg: 2
id: configuration-product-models-reduce-to-point-models
kind: claim
title: Permutation models through S_m wr S_l in product action on l-tuples of k-subsets see a word only if the underlying point models do, with the head-to-defect ratio preserved up to 4k
distinct_from:
  template-constituents-primitive-or-small-minimal-degree: that pushes template orbits down to primitive sections of vanishing relative minimal degree; this takes the product-action alternating sections that such sections are expected to be and shows they carry no more head-to-defect ratio than the imprimitive point action of the same wreath elements
  fp-simple-finite-group-models-reduce-to-alternating-constituents: that is the open identification of template sections as alternating type; this assumes nothing about how the models arise and settles the product-action case against point models, for any word and any group
  jacobson-head-concentrates-on-template-constituents: that bounds the Jacobson head by defect plus template weight in finite-group models; this answers its recorded next step (the head against A_m on m-point configurations) by reducing configurations to points
  hyperlinear-radical-has-linear-word-certificate: that is the unitary linear certificate for radical words; this is a permutation-model transfer lemma plus the Hamming analogue of the certificate, proved by tuple powers
artifacts:
  - experiments/configuration-point-models-2026-09-17/check_subset_fixed_fraction.py
---

**ESTABLISHED** (route `configuration-product-models-reduce-to-point-models-proof`, swarm-0917-w11-w11-nh-pull,
2026-09-18, unreviewed). Obstruction for a class of models, and a reduction.

**Models.** Fix a finite alphabet `X`, a finite set `R` of relator words and a word `z`, all in `F(X)`. A *Hamming
model* on a finite set `Ω` is any map `σ : X -> Sym(Ω)`, extended to words. Write:
- `h_σ(z)` for the fraction of `Ω` moved by `σ(z)`;
- `δ_σ(r)` for the fraction moved by `σ(r)`, and `δ_σ = max_(r ∈ R) δ_σ(r)`.

In normalized Hilbert-Schmidt norm, `‖σ(w) - 1‖_2^2 = 2 h_σ(w)`.

A *configuration model* of type `(m,k,l)` is a map `σ : X -> S_m wr S_l` acting in product action on `Δ_k^l`, where `Δ_k`
is the set of `k`-subsets of `[m]`. Its *point model* `σ_pt` is the imprimitive action of the same wreath elements on
`[m] x [l]`. Configuration models include the diagonal `K`-tuple power of any Hamming model on `[m]`: take `k=1`, `l=K`,
trivial top, and equal components.

**Theorem CP (configuration to points).** Assume `m >= 8k^2`.
1. **Top.** If `σ(r)` has nontrivial `S_l`-component, then `δ_σ(r) >= 1 - 1/m`.
2. **Ratio transfer.** Suppose every relator and `z` have trivial top. Then
   ```text
   h_σ(z) <= min(1, 2 k l h_pt(z)),    δ_σ(r) >= (1 - 1/e) min(1, l δ_pt(r)/2),
   h_σ(z) / δ_σ <= (e/(e-1)) max(1, 4k h_pt(z)/δ_pt).                          (CP)
   ```
   Here `h_pt` and `δ_pt` are taken for `σ_pt` on `[m] x [l]`. The number of blocks `l` is arbitrary.

**Theorem HD (Hamming dichotomy).** Let `Γ = <X | R_∞>` with `R_1 ⊂ R_2 ⊂ ...` exhausting `R_∞`. The following are equivalent:
- (a) every sequence of Hamming models `σ_n` with `δ_(σ_n, R_j) -> 0` for every `j` has `h_(σ_n)(z) -> 0`;
- (b) there are `j` and `C` with `h_σ(z) <= C δ_(σ, R_j)` for every Hamming model `σ` on every finite set.

The `K`-tuple power takes a sequence with `h/δ -> ∞` to one with defect `-> 0` and `h >= 1 - 1/e`.

**Corollary (configuration models are point models).** Let the relator windows contain a finite presentation of `St_4(J)`
and let `z` be a word for the Jacobson head `x_13(Q)`, as on `jacobson-head-concentrates-on-template-constituents`. Every
sequence of configuration models of type `(m_n, k_n, l_n)` with `m_n >= 8k_n^2`, relator defects `δ_n -> 0`,
`k_n δ_n -> 0` (automatic for bounded `k_n`) and head `h >= c > 0` has point models with `h_pt / δ_pt -> ∞` on every
window. The tops of these point models kill the head,
because they give homomorphisms of `St_4(J)` into `S_l`. By HD, their tuple powers are then Hamming models with defect
`-> 0` that see the head.

So such configuration models see the Jacobson head iff plain Hamming models do. This holds with `l` unbounded,
`k <= sqrt(m/8)` and `k δ -> 0`.

**What this kills.** The recorded next step of `jacobson-head-concentrates-on-template-constituents` was to test the head
against `A_m` acting on `m`-point configurations. That step does not test anything new.
- It gives nothing beyond Hamming point models.
- It applies to the product-action primitive sections expected in branch (M) of
  `fp-simple-finite-group-models-reduce-to-alternating-constituents`, for subset size `k <= sqrt(m/8)`.
- **Invariant.** The head-to-defect ratio `h/δ`, which (CP) preserves up to the factor `4k e/(e-1)`.
- **Where every member dies.** Step 1 of the route. The fixed fraction of a `k`-subset action is squeezed between
  `1 - 2kb` and `1 - b/2`, where `b` is the fraction of moved points.

**Not covered.**
- Subset sizes `sqrt(m/8) < k = o(m)`. The additive count of invariant subsets that are not pointwise fixed is no longer
  dominated there.
- Branch (P), primitive irreducible representations.
- Unitary models that are not permutation models.
