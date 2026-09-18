---
rg: 2
id: renormalizable-thompson-elements-are-odometer-codes
kind: claim
title: A renormalizable element of kV is exactly a bounded odometer of a brick code, and it factors onto the m-adic odometer with zero drift
distinct_from:
  renormalizable-thompson-elements-give-baumslag-solitar: that shows a height-m renormalization gives BS(1,m) in (k+1)V; this characterizes the renormalizable elements themselves and derives what they must look like.
  some-brin-thompson-element-factors-onto-an-odometer: that is the open necessary condition extracted here; this is the equivalence and the consequences.
  bs12-embeds-in-brin-thompson-2v: that is the open existence question; this turns the renormalization route to it into a search for one brick code.
---

**ESTABLISHED** through `renormalizable-thompson-elements-are-odometer-codes-proof`
(lane proof, not independently reviewed).

**Setting.** `X = C^k`. Height-`m` renormalizations `(A, φ)` of `T ∈ kV` are as in
`renormalizable-thompson-elements-give-baumslag-solitar`. A map between clopen
subsets of `X` is *brick-local* if it is a finite union of brick-to-brick prefix
replacements.
- An **m-ary brick code** is a tuple `e = (e_0, …, e_(m-1))` of brick-local
  homeomorphisms `e_i: X -> X_i` onto clopen sets with `X = X_0 ⊔ … ⊔ X_(m-1)`.
- An **odometer of `e`** is a map `T: X -> X` with `T e_i = e_(i+1)` for `i < m-1`
  and `T e_(m-1) = e_0 T`.

**Statement.**
1. **Equivalence.** `T ∈ kV` has a height-`m` renormalization iff `T` is an
   odometer of some `m`-ary brick code. Explicitly:
   - given `(A, φ)`, take `e_i = T^i φ^{-1}`;
   - given `e`, take `A = e_0 X` and `φ = e_0^{-1}`.
2. **Odometer factor.** For such `T`, let the digit of `x` be the `i` with
   `x ∈ X_i`, and put `S x = e_i^{-1} x`. Then
   `π(x) = Σ_(j>=0) digit(S^j x) m^j` is a continuous surjection
   `X -> Z_m` with `π ∘ T = π + 1`.
3. **Consequences.**
   - (a) `T` has no periodic points.
   - (b) Every `T`-invariant Borel probability measure `μ` has zero drift:
     `∫ δ_T dμ = 0 ∈ Z^k`, where `δ_T` is the exponent cocycle of
     `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`.
   - (c) For every word `w` of length `j`, with `e_w = e_(w_0) ∘ … ∘ e_(w_(j-1))`,
     `T^(m^j) e_w = e_w T`. So `T^(m^j)` is `e_w T e_w^{-1}` on each `e_w X`, and
     its table length is `O(j)`.
4. **The naive code fails.**
   - If every `e_i` is a single prefix insertion `x ↦ (p_(i,1) x_1, …, p_(i,k) x_k)`
     and `m = 2`, then up to relabelling `e` is the standard code: `0·` and `1·` in
     one coordinate.
   - Its only continuous odometer is `τ × id`, with `τ` the binary odometer, and
     `τ × id ∉ kV`.
   - So a working code must rearrange or move material between coordinates.

**What this says about the search.** The renormalization route to
`bs12-embeds-in-brin-thompson-2v` needs a brick code whose recursive odometer
has a finite table. Item 2 gives a test that costs no construction: a
candidate must already factor onto an infinite odometer. That test is
`some-brin-thompson-element-factors-onto-an-odometer`.
- Elements of the topological full group of the full shift fail it, since they
  fix the two constant configurations.
- The natural candidate is a SMART-type machine. Callard--Salo
  (arXiv:2208.00685v3) use the level timings `f(k+1) = 3 f(k) + 4` of SMART.
  An exact height-3 renormalization would need `f(k+1) = 3 f(k)`, i.e. no additive
  defect. This is a precise design target.
