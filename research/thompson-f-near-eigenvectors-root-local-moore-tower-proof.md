---
rg: 2
id: thompson-f-near-eigenvectors-root-local-moore-tower-proof
kind: route
title: Run Moore's weighted derivative chain on f squared with mass kept, read the tower off the right spine, and translate range-tree subtrees into pointed-forest trees
target: thompson-f-near-eigenvectors-carry-a-root-local-moore-tower
requires: []
artifacts:
  - experiments/thompson-f-root-local-tower-2026-09-17/dictionary_check.py
  - experiments/thompson-f-root-local-tower-2026-09-17/dictionary_check.out
---

**Sources.** J. T. Moore, *Fast growth in the Folner function for Thompson's group F*,
arXiv:0905.1118v7 (Groups Geom. Dyn.). Lemma names are the LaTeX labels of the arXiv source. Every
lemma used is quoted below as stated there. Nothing else is imported.

**Moore's conventions.**
- `Γ = {x0, x1, x0^(−1), x1^(−1)}`, and `f·g` is `f` followed by `g`.
- `(L_f, R_f)` is the reduced diagram of `f`: `f` carries the leaves of `L_f` in order onto the leaves
  of `R_f`.
- `𝒯` is the set of finite binary trees, identified with their sets of leaves (binary strings).
  - `F` acts partially on the right: `T·g` is defined when `T` dominates (is refined by) a domain tree
    of `g`.
  - For a generator `γ` and `f` with `R_f` dominating the length-4 tree, `R_(f·γ) = R_f·γ` and
    `L_(f·γ) = L_f`.
- A *weighted ε-Folner set* is a finitely supported `μ ≥ 0` on a set with a partial action, satisfying
  `Σ_γ Σ_s |μ(s·γ) − μ(s)| < ε μ(S)`, where `μ(s·γ) = 0` if `s·γ` is undefined.
- A *marginal* set is defined in Moore's Section 3.

**Quoted lemmas.**
- **(M1) Folner_hom_prop.** Suppose `μ` is weighted `ε`-Folner on `S`, and `h : S → T` satisfies
  `h(s·γ) = h(s)·γ` (both defined) whenever `μ(s) + μ(s·γ) > 0`. Then `h_* μ` is weighted
  `ε`-Folner.
- **(M2) The unnamed lemma after `marginal`.** If `E` is marginal, there is `C_E` with
  `μ(E) < C_E ε μ(S)` for every weighted `ε`-Folner `μ`.
- **(M3) marginal->Folner.** If `E` is marginal (with nonempty complement), there is `C` such that
  `C ε ≤ 1` implies that `μ ↾ (S ∖ E)` is weighted `C ε`-Folner.
- **(M4) not_in_marginal.** For each binary string `u`, `{f ∈ F : u` is not extended by an element of
  `R_f}` is marginal in the right action of `F` on itself.
- **(M5) partial_growth, and the definition of ∂.**
  - `∂T` is dominated by `T`.
  - Its interior leaves `u` satisfy either `2|T/u| ≤ |T/u'|` for all interior `u <_lex u'`, or the
    reverse inequality for all such pairs.
  - If `∂T` has `n` leaves, `T` has more than `2^(n−2)` leaves.
- **(M6) partial_compatible.** If `g` acts properly on `∂T`, then `∂(T·g) = (∂T)·g`.
- **(M7) proper_act.** `{T : Γ` does not act properly on `∂T}` is marginal. Its proof shows that
  `E** = ∪_(i ≤ 16) E*·x0^i ∪ {T : T·x0^(−i)` undefined for some `i ≤ 16}` is marginal, and that for
  `T ∉ E**` one of the following holds:
  - `2|T/1^i 0| < |T/1^(i+1) 0|` for all `i < 16`;
  - `2|T/1^(i+1) 0| < |T/1^i 0|` for all `i < 16`.

These are Moore's displayed assertions, lines 1234 to 1243 of the source.

**The constant.** `K_0` is the maximum of the following constants, and of 2:
- the constants `C_E` of (M2) for the marginal sets of (M4) with `u` ranging over the 16 strings of
  length 4;
- the constant of (M3) for their union, and for the set of (M7);
- the constant `C_E` of (M2) for the set of (M7) and for `E**`.

These are finitely many constants attached to fixed marginal sets, so `K_0` is absolute.

## Step 1. From l2 to weighted Folner

Let `F ≥ 0` be a finitely supported unit vector in `l2(F)`, with `η = 1 − ⟨F, P F⟩`.
- **η is positive.** If `η = 0`, then `PF = F` with `||ρ_γ F|| = ||F||`, so `F` is invariant under
  every right translation. Then `F` is constant, which is impossible for a unit vector.
- **The energy identity.** Each `ρ_γ` is unitary, so
  `Σ_γ ||ρ_γ F − F||² = Σ_γ (2 − 2⟨F, ρ_γ F⟩) = 8 − 8⟨F, PF⟩ = 8η`.
- **The Folner bound.** Put `μ = F²`, so `μ(F) = 1`. Then
  `Σ_γ Σ_s |μ(s·γ) − μ(s)| = Σ_γ Σ_s |F(sγ) − F(s)| (F(sγ) + F(s))`.
  - By Cauchy-Schwarz this is at most `Σ_γ ||ρ_γ F − F|| · ||ρ_γ F + F|| ≤ 2 Σ_γ ||ρ_γ F − F||`.
  - Cauchy-Schwarz over the four `γ` bounds that by `2 (4 · 8η)^(1/2) = 8√2 √η`.
  - Since `η > 0`, this is strictly below `12√η`.

So `μ` is a weighted `ε`-Folner set with `ε = 12√η`. More generally, it is weighted `ε`-Folner for every
`ε > 8√2 √η`.

## Step 2. Trees, with mass kept

Let `U` be the tree of all 16 strings of length 4, and let `A_0 = {y ∈ F : R_y` dominates `U}`.
- **The removed set.** Its complement is the union of the sets of (M4) over `u ∈ U`, which is marginal.
  By (M2), `μ(F ∖ A_0) < K_0 ε`.
- **The restriction.** By (M3), `μ ↾ A_0` is weighted `K_0 ε`-Folner, since `K_0 ε ≤ 1`.
- **The pushforward.** Put `h_0(y) = R_y` and `ν_0 = (h_0)_*(μ ↾ A_0)`. We check the hypothesis of (M1)
  for `μ ↾ A_0`. Take `γ` with `(μ ↾ A_0)(y) + (μ ↾ A_0)(yγ) > 0`.
  - If `y ∈ A_0`, then `R_(yγ) = R_y·γ` by Moore's observation in the proof of Folner->trees.
  - If `yγ ∈ A_0`, apply the same observation to `yγ` and `γ^(−1)`. It gives `R_y = R_(yγ)·γ^(−1)`,
    hence `R_y·γ = R_(yγ)`.

  So by (M1), `ν_0` is weighted `K_0 ε`-Folner on `𝒯`, with total mass `μ(A_0)`.

This is Moore's Folner->trees with `1_A` replaced by `μ`. His proof does not use that `μ` is an
indicator.

## Step 3. n derivatives, with mass kept

Let `𝒜 = {T ∈ 𝒯 : Γ` acts properly on `∂T}`. Its complement is marginal by (M7). For `j ≥ 1` define
`Y_j = {y ∈ A_0 : ∂^l R_y ∈ 𝒜` for `0 ≤ l < j}`, with `Y_0 = A_0`, and
`ν_j = (∂^j ∘ h_0)_*(μ ↾ Y_j)`.

**Claim.** If `K_0^(j+1) ε ≤ 1`, then `ν_j` is weighted `K_0^(j+1) ε`-Folner. Moreover
`μ(Y_(j−1) ∖ Y_j) < K_0^(j+1) ε`.

*Proof, by induction on `j`.* The case `j = 0` is Step 2.
- **The pushforward identity.** For any map `h` and set `B`, `(h_* λ) ↾ B = h_*(λ ↾ h^(−1) B)`.
  Hence `ν_(j−1) ↾ 𝒜 = (∂^(j−1) ∘ h_0)_*(μ ↾ Y_j)` and `ν_j = ∂_*(ν_(j−1) ↾ 𝒜)`.
- **The mass bound.** `ν_(j−1)` is `K_0^j ε`-Folner with total mass at most 1. By (M2),
  `μ(Y_(j−1) ∖ Y_j) = ν_(j−1)(𝒯 ∖ 𝒜) < K_0 · K_0^j ε`.
- **The restriction.** By (M3), `ν_(j−1) ↾ 𝒜` is `K_0^(j+1) ε`-Folner.
- **Equivariance.** Take `γ` with `(ν_(j−1) ↾ 𝒜)(T) + (ν_(j−1) ↾ 𝒜)(T·γ) > 0`.
  - If `T ∈ 𝒜`, then `∂(T·γ) = (∂T)·γ` by (M6).
  - If `T·γ ∈ 𝒜`, apply (M6) to `T·γ` and `γ^(−1)`. It gives `∂T = ∂(T·γ)·γ^(−1)`.
- **Conclusion.** By (M1), `ν_j` is `K_0^(j+1) ε`-Folner. This is Moore's partial_marginalize with its
  mass kept. □

## Step 4. The last level

Assume `K_0^(n+1) ε ≤ 1`, so Step 3 applies for `j ≤ n`.
- **The last removal.** Let `Y = {y ∈ Y_n : ∂^n R_y ∉ E**}`. By (M2) for `E**`,
  `μ(Y_n ∖ Y) = ν_n(E**) < K_0^(n+2) ε`.
- **The total loss.**
  `μ(F ∖ Y) < ε(K_0 + K_0² + ... + K_0^(n+2)) ≤ 2 K_0^(n+2) ε = 24 K_0^(n+2) √η`, using `K_0 ≥ 2`.
- **The doubling.** Fix `y ∈ Y` and put `S = ∂^n R_y`, which is not in `E**`.
  - `S·x0^(−16)` is defined, so `S` dominates the domain tree `{0, 10, ..., 1^16 0, 1^17}` of
    `x0^(−16)`.
  - In particular `S` is nontrivial, and `S/0` and `S/1^16 0` are nonempty.
  - By (M7), one of two cases holds.
- **Increasing case.** `|S/1^16 0| > 2^16 |S/0| ≥ 2^16`. Put `v = 1^16 0`.
- **Decreasing case.** `|S/10| > 2^15 |S/1^16 0| ≥ 2^15`. Put `v = 10`.

In both cases `|∂^n R_y / v| ≥ 2^15`.

## Step 5. The subtree-local chain

**Lemma (local partial_growth).** For every `T ∈ 𝒯` and every binary string `v`,

`|T/v| ≥ 2^(|∂T/v| − 2) − 1`.

*Proof.* Let `m = |∂T/v|`. For `m ≤ 2` the right side is at most 0, so assume `m ≥ 3`.
- **Interior leaves below `v`.** `∂T` has exactly two end points (its minimum and maximum leaves). So
  at least `m − 2` of its leaves extending `v` are interior. Call them `u_1 <_lex ... <_lex u_(m−2)`.
- **Doubling.** By the monotone condition in (M5), the numbers `|T/u_l|` satisfy one of two chains:
  `2|T/u_l| ≤ |T/u_(l+1)|` for all `l`, or `2|T/u_(l+1)| ≤ |T/u_l|` for all `l`.
- **Each term is at least 1.** `∂T` is dominated by `T`, so every leaf of `∂T` is extended by some leaf
  of `T`, and `|T/u_l| ≥ 1`.
- **The sum.** Hence the sizes, in increasing or in decreasing order, are at least `1, 2, 4, ...`, and
  they sum to at least `2^(m−2) − 1`.
- **Disjointness.** The `u_l` are pairwise incomparable and all extend `v`. So the leaf sets of `T`
  below them are disjoint subsets of the leaves of `T` below `v`. □

This is Moore's partial_growth with `v` equal to the empty string, localised to a subtree. His proof
gives it without change.

**Induction.** Fix `y ∈ Y` and `v` from Step 4, and put `a_j = |∂^j R_y / v|` for `0 ≤ j ≤ n`.
- By Step 4, `a_n ≥ 2^15`.
- By the lemma applied to `T = ∂^j R_y`, `a_j ≥ 2^(a_(j+1) − 2) − 1`.

We claim `a_(n−k) ≥ 2 exp_(k+4)(0)` for `0 ≤ k ≤ n`.
- The case `k = 0` is `2^15 ≥ 32 = 2 exp_4(0)`.
- For the step, put `E = exp_(k+4)(0) ≥ 16`. Then
  `a_(n−k−1) ≥ 2^(2E − 2) − 1 ≥ 2^(E+1) = 2 exp_(k+5)(0)`,
  since `2E − 2 ≥ E + 2` for `E ≥ 4`.

Taking `k = n` gives `|R_y / v| ≥ 2 exp_(n+4)(0)` for some `v ∈ {10, 1^16 0}`, for every `y ∈ Y`.
Together with Step 4 this proves Theorem A for finitely supported `F`, including its more precise form.

## Step 6. The dictionary to pointed forests

**Notation.** This follows `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`.
- `G = ⟨s_0, s_1⟩ ≤ PL(R)`, with `s_0(t) = t + 1`.
- `s_1` is `t` on `t ≤ 0`, `2t` on `[0, 1]`, and `t + 1` on `t ≥ 1`.
- For a pointed forest `v = (T_0, ..., T_(m−1); i)` with `n` leaves in all:
  - `E(v)` maps `[k, k+1]` onto the block of `T_(i+k)` by `t ↦ a_j + h_(T_j)(t − k)`, where `j = i + k`
    and `a_j = Σ_(q<j) |T_q|`;
  - `E(v)` is `t ↦ t + i` for `i + k < 0`, and `t ↦ t + i + n − m` for `i + k ≥ m`.
- Moves are `E(v') = E(v) ∘ s` for `s ∈ {s_0^(±1), s_1^(±1)}`.
- By `thompson-f-one-sided-forest-windows-are-norm-lossless`, on `E(R)` these edges are exactly the edges
  of the move graph `Γ_R`.

**(a) Conjugacy.** Let `φ : (0,1) → R` map the dyadic interval of `1^(k+1) 0` affinely onto `[k, k+1]`
for `k ≥ 0`, and the interval of `0^k 1` affinely onto `[−k, −k+1]` for `k ≥ 1`.
- Let `X_0` be the diagram `(00, 01, 1) → (0, 10, 11)` and `X_1` the diagram
  `(0, 100, 101, 11) → (0, 10, 110, 111)`. These are Moore's generators up to inversion, so `Γ` is
  unchanged.
- Leaf by leaf, `φ X_0 φ^(−1) = s_0`:
  - `01 → 10` sends `[−1, 0]` to `[0, 1]`;
  - `00 → 0` shifts the left units;
  - `1 → 11` shifts the right units.
- Similarly `φ X_1 φ^(−1) = s_1`:
  - `0` is fixed;
  - `100 → 10` and `101 → 110` double `[0, 1]` onto `[0, 2]`;
  - `11 → 111` shifts the rest.

Put `ψ(x) = φ^(−1) x φ` and `y(v) = ψ(E(v))^(−1)`. The map `v ↦ y(v)` is injective, because `E` is
injective.

**(b) Moves are right multiplications.** From `E(v') = E(v) ∘ s` we get `ψ(E(v')) = ψ(E(v)) ∘ X`, with
`X = ψ(s) ∈ Γ`. Hence `y(v') = X^(−1) ∘ y(v)`, which in Moore's product is `y(v)·X^(−1)`.
- So `y` identifies `Γ_R` with the subgraph of the right Cayley graph of `F` induced on `y(R)`.
- For `f` on `R`, put `F = f ∘ y^(−1)` on `y(R)` and 0 elsewhere. Then
  `⟨F, P F⟩ = (1/4) Σ_s Σ_γ F(s) F(sγ) = (1/4) Σ_(v ~ v' in Γ_R) f(v) f(v') = ⟨f, K f⟩/4`,
  and so `η(F) = η(f)` exactly.

**(c) An explicit diagram.** Fix `N ≥ max(i, m − i, 16)`, and let `u_k` be the address of the unit
`[k, k+1]`: `1^(k+1) 0` for `k ≥ 0` and `0^(−k) 1` for `k < 0`. Let `L` be the tree with leaves
- `0^(N+1)`;
- `u_k w` for `−N ≤ k < N` and `w` a leaf of `T_(i+k)`, where `T_j` is the trivial tree for `j` outside
  `[0, m)`;
- `1^(N+1)`.

Let `R` have, in the same order, the leaves
- `0^(N − i + 1)`;
- `u_(a + q)` for the `q`-th leaf of `T_(i+k)`, where `a = a_(i+k)` (or the shifted value outside
  `[0, m)`);
- `1^(N + n + i − m + 1)`.

**`(L, R)` represents `g = ψ(E(v))`.**
- *Middle leaves.* On the interval of `u_k w`, `φ` is affine onto the dyadic piece of `[k, k+1]` named
  by `w`. `E(v)` maps that piece affinely onto `[a + q, a + q + 1]`, and `φ^(−1)` maps that affinely onto
  the interval of `u_(a+q)`.
- *Tails.* On `0^(N+1)` the composite sends `0^k 1 s` to `0^(k−i) 1 s` for `k ≥ N + 1`. That is the
  prefix replacement `0^(N+1) → 0^(N−i+1)`. The right tail is the same.
- *Check.* Part (B) of the dictionary check confirms this on 400 random forests.

**(d) Domination.** The reduced diagram `(L_g, R_g)` comes from `(L, R)` by cancelling carets. So `L`
dominates `L_g`.
- For any `u` with an extension in `L`, either `L_g/u` is a tree dominated by `L/u`, or `L_g` has a
  leaf that is a prefix of `u`, and then `|L_g/u| ≤ 1`.
- Either way `|L_g/u| ≤ |L/u|`.
- With `u = u_k` for `0 ≤ k < N`, this reads `|L_g / 1^(k+1) 0| ≤ |T_(i+k)|`. Part (C) of the check
  confirms it, and in fact finds equality of shapes whenever `T_(i+k)` is nontrivial.

Since the diagram of `g^(−1)` is `(R_g, L_g)`, we have `R_(y(v)) = L_g`. Hence
`|R_(y(v)) / 10| ≤ |T_i|` and `|R_(y(v)) / 1^16 0| ≤ |T_(i+15)|`.

**Corollary B for finitely supported `f`.** Apply Theorem A to `F = f ∘ y^(−1)`. The bad set of
Corollary B is contained in the `y`-preimage of the complement of `Y`.

## Step 7. Infinite support, and Corollary C

**Truncation.** Let `F` be a unit vector (on `F` or on `R`) with deficit `η > 0` and infinite support.
Assume `12 K_0^(n+1) √η ≤ 1`.
- Let `F_N` be the normalised restriction of `F` to an exhausting sequence of finite sets. Then `F_N → F`
  in `l2`, and `η(F_N) → η` because `P` (or `K`) is bounded.
- For large `N`, `8√2 √η(F_N) < 12√η`. By Step 1, `F_N²` is then weighted `ε`-Folner with the same
  `ε = 12√η`.
- Steps 2 to 6 used only this `ε`. So `F_N²(B) ≤ 24 K_0^(n+2) √η`, where `B` is the fixed bad set of
  Theorem A or Corollary B.
- Since `F_N²(B) → F²(B)`, the bound holds for `F`.

The case `η = 0` does not occur (Step 1).

**Corollary C.** Assume every `v` in the support of `f` has `|T_i| < N` and `|T_(i+15)| < N`. Let `n`
be the least integer `≥ 0` with `2 exp_(n+4)(0) ≥ N`, so that `n ≤ log* N`.
- If `12 K_0^(n+1) √η ≤ 1`, Corollary B gives `1 ≤ 24 K_0^(n+2) √η`.
- Otherwise `√η > 1/(12 K_0^(n+1))`.
- Either way `√η ≥ 1/(24 K_0^(n+2))`, that is `η ≥ (1/576) K_0^(−2n−4) ≥ (1/576) K_0^(−2 log* N − 4)`.

**The half-mass form.** Take `n = ⌊log_(K_0)(1/(48√η))⌋ − 2` when this is `≥ 0`.
- Then `24 K_0^(n+2) √η ≤ 1/2`, and `12 K_0^(n+1) √η ≤ 1/(4 K_0) ≤ 1`.
- So Corollary B applies, and at least half the mass sees `max(|T_i|, |T_(i+15)|) ≥ 2 exp_(n+4)(0)`.

## What is and is not proved

- Every step is either one of Moore's lemmas (M1) to (M7), quoted with its hypotheses, or a direct
  argument written out above.
- The only changes to Moore's text are two.
  - The weight `μ` is kept through Folner->trees and partial_marginalize, where Moore restricts to
    supports. His proofs are already written for weighted sets, except Folner->trees, and Step 2 checks
    that one.
  - The growth is localised to a subtree (Step 5), and the right-spine doubling (M7) is used at the last
    level.
- `K_0` is not computed. It exists because all marginal sets used are fixed.
- Nothing is claimed about `thompson-f-is-amenable`.
