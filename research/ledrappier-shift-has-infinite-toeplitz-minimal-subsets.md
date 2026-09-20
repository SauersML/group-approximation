---
rg: 2
id: ledrappier-shift-has-infinite-toeplitz-minimal-subsets
kind: claim
title: Ledrappier's shift has infinite minimal subsets, so (FL) is false; an explicit non-periodic Toeplitz point is built from F_4-twisted Sierpinski gaskets shifted by a non-rational 2-adic integer, untwisted by the trace against ζ^(v_1 − v_2). Toeplitz points with only odd-index period lattices are periodic and those with only 2-power lattices accumulate on 0, so a mixed period with the prime 2 and some odd prime is forced; the examples are almost automorphic, so they cannot carry T1
distinct_from:
  ledrappier-shift-has-only-finite-minimal-subsets: that states (FL) as an open crux; this refutes it with an explicit Toeplitz point, and shows why every Toeplitz example must have a period mixing the prime 2 with some odd prime.
  free-minimal-triangle-permutive-sft-exists: that seeks free minimal sub-SFTs of quasigroup spacetimes; the minimal sets here are subshifts, not claimed to be SFTs, and they are Toeplitz, so the sub-SFT question is untouched.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - ledrappier-shift-has-only-finite-minimal-subsets
  - algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier
  - algebraic-t1-sets-carry-free-distal-commutator-actions
```

**ESTABLISHED (lane bh-bq2, 2026-09-19; refereed PASS by bh-ref-c, a7b6ad0f7b, no prior found; no priority
claimed).**
- The construction is in the spirit of the automatic space-time diagrams of linear cellular automata
  (Rowland–Yassawi, arXiv:1811.01256) and of the Pascal/Sierpinski structure of `x ↦ x + σx`.
- Whether an infinite minimal subset of Ledrappier's shift is already in the literature was not settled by
  our searches.

## Statement

Let `X_L = {x ∈ F_2^(Z^2) : x(v) + x(v+e_1) + x(v+e_2) = 0}`, `F_4 = F_2(ζ)` with `ζ^2 + ζ + 1 = 0`, and
`m(v) = v_1 − v_2`.

1. **An infinite minimal subset.** Fix a 2-adic integer `α ∈ Z_2 \ Q`, for example `Σ_k 2^(k^2)`, and
   integers `a_k ≡ α (mod 2^(k+1))`. For `N_k = 2^(k+1)` and `j, l ∈ [0, N_k)`, put
   `G_k(j, l) = ζ^(j + 2l)` if `j` and `l` have disjoint binary digits, and `0` otherwise. Define
   ```
   h_k(v) = G_k((a_k − v_1) mod N_k, (a_k − v_2) mod N_k),   x = Σ_(k ≥ 0) ζ·h_k,
   y(v) = Tr_(F_4/F_2)(x(v) ζ^(m(v))).
   ```
   Then the sum defining `x` is locally finite, `y ∈ X_L`, `y` is uniformly recurrent (indeed Toeplitz, with
   period lattices of the form `2^K{λ : λ_1 ≡ λ_2 mod 3}`), and `y` is not periodic. So the orbit closure of
   `y` is an **infinite minimal subset of `X_L`**, and (FL) is false.
2. **Mixing is forced.**
   - (a) **Odd lattices are rigid.** If `x ∈ X_L` is constant on one coset of a sublattice `Λ ≤ Z^2` of odd
     index, then `x` is periodic. So a Toeplitz point of `X_L` whose period lattices all have odd index is
     periodic.
   - (b) **2-power lattices are dead too.** A Toeplitz point with 2-power periods has `0` in its orbit closure
     (`ledrappier-shift-has-only-finite-minimal-subsets`, Evidence).

   So some period must mix the prime 2 with an odd prime; the example uses `3·2^K`.
3. **Consequence for T1.** These minimal sets are almost automorphic, since they are Toeplitz. By
   `algebraic-t1-sets-carry-free-distal-commutator-actions`, an algebraic T1 set is never a proximal extension
   of its maximal equicontinuous factor. So no T1 set lies over them in the sense of
   `algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier`: the row projections `N_w` of a T1 set may be
   almost automorphic, but the joint set cannot be. **Algebraic T1 stays open**, now with the knowledge that its
   row projections have somewhere to live.

## Proof

**Step 1 (gaskets are periodic points of an `F_4`-twist).** Let `ℓ = 1 + ζX_1 + ζ^2X_2` in
`R_k = F_4[X_1, X_2]/(X_1^(N_k) − 1, X_2^(N_k) − 1)`.
- *Coefficients.* Since `N_k − 1` has all binary digits equal to 1, the multinomial coefficient of
  `1^i (ζX_1)^j (ζ^2X_2)^l` in `ℓ^(N_k − 1)` is odd iff `i, j, l` have disjoint digits (Lucas). So
  `ℓ^(N_k − 1) = Σ_(j, l) G_k(j, l) X_1^j X_2^l`.
- *It is killed by `ℓ`.* In characteristic 2, `ℓ^(N_k) = 1 + ζ^(N_k) + ζ^(2N_k) = 1 + ζ + ζ^2 = 0` in `R_k`.
  Reading off the coefficient of `X^w` in `ℓ·ℓ^(N_k−1) = 0` gives
  `G_k(w) + ζG_k(w − e_1) + ζ^2 G_k(w − e_2) = 0` (mod `N_k`).
- *So each `h_k` lies in `X'`.* With `w = (a_k, a_k) − v`, this says `h_k ∈ X'`, where
  `X' := {β ∈ F_4^(Z^2) : β(v) + ζβ(v+e_1) + ζ^2β(v+e_2) = 0}`. `h_k` is `N_k Z^2`-periodic.

**Step 2 (local finiteness).**
- *Supports.* `v ∈ supp h_k` iff the lowest `k+1` digits of the 2-adic integers `α − v_1` and `α − v_2` are
  disjoint.
- *Claim: if `β ∈ Z_2` and `β` and `β + d` (`d ∈ Z`) have disjoint digit sets, then `β ∈ Q`.*
  - Disjointness means `β + (β+d) = 2β + d` has no carries, so `β` is a submask of `2β + d`.
  - If `β` is not eventually constant in its digits, the carries or borrows from adding `d` to `2β` die out
    above some position `P`. Beyond `P`, digit `i` of `2β + d` is digit `i−1` of `β`.
  - So digit `i` of `β` being 1 forces digit `i − 1` of `β` to be 1, for all `i > P`. The infinite digit set
    of `β` then contains `[P, ∞)`, and `β` is eventually all 1s, hence rational.
- *Conclusion.* Since `α ∉ Q`, each `v` has an overlap position `p_v`, and `v ∉ supp h_k` for `k ≥ p_v`. So
  `x = Σ ζ h_k` is locally finite, and `x ∈ X'` because `X'` is closed.

**Step 3 (Toeplitz).**
- Let `H_K = {v : the lowest K digits of α − v_1 and α − v_2 are disjoint}`. It is `2^K Z^2`-periodic and
  contains `supp h_k` for every `k ≥ K`.
- Off `H_K`, `x` equals the `2^K Z^2`-periodic sum `p_K = Σ_(k<K) ζh_k`.
- Take a finite window `u + B` and `K > max_(v ∈ u+B) p_v`. Then `(u + B + 2^Kλ) ∩ H_K = ∅` for every `λ`.
  So `x` repeats on `u + B` along all of `2^K Z^2`.

**Step 4 (untwisting).** `m(v + e_1) = m(v) + 1` and `m(v + e_2) = m(v) − 1`, so
`y(v) + y(v+e_1) + y(v+e_2) = Tr(ζ^(m(v)) [x(v) + ζx(v+e_1) + ζ^2 x(v+e_2)]) = 0`, and `y ∈ X_L`.
- If `λ ∈ 2^K Z^2` has `λ_1 ≡ λ_2 mod 3`, then `m(v + λ) ≡ m(v)`. So `y` repeats on `u + B` along
  `2^K{λ : λ_1 ≡ λ_2 mod 3}`, a lattice of finite index.
- Hence `y` is uniformly recurrent.

**Step 5 (not periodic).** Fix `P ≥ 0` and an odd `n`.
- *The two points.* Choose an integer `u_0` with `u_0 ≡ α − 2^(P+1) mod 2^(P+2)`, and put `u = (u_0, u_0)`.
  Then `β := α − u_0` is `0` in digits `0..P` and `1` in digit `P+1`. Let `u' = u + 2^P n(1,1)`; then
  `β − 2^P n` has digit `P` equal to 1 in both coordinates.
- *Terms with `k > P`.* Both coordinates of `u` share digit `P+1`, so `u ∉ supp h_k`. Both coordinates of `u'`
  share digit `P`, so `u' ∉ supp h_k` for `k ≥ P`.
- *Terms with `k < P`.* These are `2^P`-periodic, so they agree at `u` and `u'`.
- *The term `k = P`.* `h_P(u) = G_P(0, 0) = 1`, while `h_P(u') = 0`.
- *Conclusion.* `x(u) − x(u') = ζ`, and since `m(u) = m(u') = 0`, `y(u) − y(u') = Tr(ζ) = 1`. So `y` is not
  invariant under `2^P n (1,1)` for any `P ≥ 0` and odd `n`, hence under no nonzero multiple of `(1,1)`, and
  `y` is not periodic. ∎

**Proof of 2(a).** Suppose `x` is constant on `c + Λ`, with `N Z^2 ⊆ Λ` and `N` odd. For each `λ ∈ Λ`, the
point `q_λ = x + σ_λ x ∈ X_L` vanishes on `c + Λ`.
- *Each `q_λ` lies in a fixed finite group.* `q_λ` annihilates `u^c A_Λ`, where `A_Λ = F_2[u^λ : λ ∈ Λ]`.
  The fraction field of `A_Λ` is all of `k = F_2(s)`: it contains `F_2(s^N, t^N) = k` by
  `char-2-benoist-quint-needs-the-homogeneous-form`, Proof of 3. So `u^c A_Λ` has full rank in the finite
  `A_Λ`-module `A`, the quotient `A/u^cA_Λ` is finite, and `q_λ` lies in the finite group
  `Q = (u^c A_Λ)^⊥`.
- *A crossed homomorphism.* `Q` is `Λ`-invariant, and `q_(λ+μ) = q_λ + σ_λ q_μ`. On the finite-index subgroup
  `Λ' ≤ Λ` acting trivially on `Q`, `λ ↦ q_λ` is a homomorphism into the finite group `Q`. Its kernel has
  finite index, and `σ_λ x = x` there.
- *Toeplitz points.* The skeleton of a Toeplitz point contains a full coset on which the point is constant. ∎

## Lesson for general BH

- **Two obstructions cancel.** Frobenius kills the 2-power hierarchy of Ledrappier's shift, since there are no
  `2^k`-periodic points. Odd lattices are rigid, since constancy on one coset forces periodicity. Twisting by
  the cube root of unity cancels the Frobenius obstruction: over `F_4`, `ℓ^(2^k)` is `ℓ` evaluated at 1, which
  is `1 + ζ + ζ^2 = 0`. So Sierpinski gaskets become periodic points, and a non-rational 2-adic shift glues them
  into a Toeplitz point.
- **What this means for T1.** Minimal sets of algebraic rows exist in abundance, but the ones this mechanism
  makes are almost automorphic. So T1, which needs a minimal set that is not a proximal extension of its
  equicontinuous factor, is not settled by the existence question: the obstruction must be sought in the
  distal and weakly mixing layers.
