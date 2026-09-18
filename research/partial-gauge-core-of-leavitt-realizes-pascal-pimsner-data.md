---
rg: 2
id: partial-gauge-core-of-leavitt-realizes-pascal-pimsner-data
kind: claim
title: The fixed ring R of the Leavitt algebra L_Q(1,2) under the letter-2 grading has an isometric frame over the Pascal core with K_0-action ×(1−t), matching the non-scalar-index target, but R has a character, so it is not simple
distinct_from:
  torsion-k1-modulo-central-scalars-kills-scalar-symbols: that identifies the target Pimsner data (1 − [X] injective with rank-one cokernel spanned by [1_B]); this realizes those data inside a finitely presented ring and finds the obstruction to simplicity.
  isometric-shift-frames-over-uhf-bases-fail-the-k-budget: that kills frames of rational index over matricial bases; here the index is the non-scalar class (1 − t)[1_B], so its item 1 does not apply.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the gate; this is a design attempt for its infinite-rank K_0(B) room.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** for items 1–4 through `partial-gauge-core-of-leavitt-realizes-pascal-pimsner-data-proof`.
This is an elementary lane proof (gq-k2-q), not independently reviewed. Item 5 is conditional on the Pimsner
sequence `(P)`, and item 6 is open.

## Setting

- `L = L_Q(1,2)`, with `s_1, s_2, t_1, t_2`, `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`. It is finitely presented
  and simple.
- Grade `L` by `deg_2`, with `deg s_2 = 1`, `deg t_2 = −1`, and the other generators in degree `0`. Let `R` be the
  degree-0 part.
- Let `B ⊆ R` be the span of the `s_μ t_ν` with `|μ| = |ν|` and equal numbers of `2`s. This is the core for both
  gradings.

## Statement

1. **The Pascal core.** `B = colim_n B_n`, with `B_n = ⊕_(k=0)^n M_(binom(n,k))(Q)`, the span of the `s_μ t_ν` with
   `|μ| = |ν| = n` and `k` letters `2`.
   - The inclusion `B_n -> B_(n+1)`, `s_μ t_ν = s_(μ1) t_(ν1) + s_(μ2) t_(ν2)`, sends block `k` to blocks `k` and
     `k+1`. This is the Pascal Bratteli diagram.
   - `K_0(B) ≅ Z[t]`, via `[e_(n,k)] ↦ t^k (1−t)^(n−k)`, with `[1_B] = 1`.
2. **The frame.** `s = t_1` and `t = s_1` lie in `R`, and `s t = 1`, `t s = s_1 t_1 = p ∈ B`. So this is an isometric
   frame of size one over `B`. Its endomorphism `φ(b) = s_1 b t_1` maps `B` into `pBp`.
3. **Its `K_0`-action is `A = ×(1−t)`.** `φ(s_μ t_ν) = s_(1μ) t_(1ν)` keeps the number of `2`s, so it sends vertex
   `(n,k)` to `(n+1,k)`, of class `(1−t)·t^k (1−t)^(n−k)`.
   - Hence `1 − A = ×t` is injective on `Z[t]`, and `coker(1 − A) = Z[t]/(t) ≅ Z`, with `[1_B] ↦ 1`.
   - The index `[p] = (1−t)[1_B]` is not a rational multiple of `[1_B]`.
4. **`R` is not simple.** Let `V` be spanned by the infinite words `w` over `{1, 2}` that are eventually `1`, with
   `s_i e_w = e_(iw)` and `t_i e_(iw) = e_w`, `t_i e_(jw) = 0` for `j != i`. This is an `L`-module, since every word
   begins with `1` or `2`.
   - Elements of `R` preserve the number of `2`s. So `R` preserves the line `Q e_(1^∞)`.
   - This gives a character `χ : R -> Q`, with `χ(s_1) = χ(t_1) = 1` and `χ(s_2 t_2) = 0`.
   - `ker χ` is a proper nonzero ideal.
5. **Conditional on `(P)`.** Suppose `(P)` holds for `(R, B, φ)`, and tensor with a central `Q̄` (so `K_*(B)` is
   replaced by its ultramatricial version over `Q̄`).
   - `K_0(R) ⊇ coker(1 − A) ⊗ Q`, and `[1_R]` has infinite order.
   - `K_1(R)` is scalars plus torsion, and `K_2(R) = 0`.
   - So these are exactly the target data of `torsion-k1-modulo-central-scalars-kills-scalar-symbols`.
6. **Open.** Whether `R` is finitely generated, or finitely presented, over `Z`.

## Reading

- The character of item 4 is the boundary point `t = 0` of the Pascal cone, the letter frequency of `2` being `0`.
  The Pascal dimension group has order ideals at the boundary, `(t)` and `(1−t)`. The ideal `(t)` is invariant
  under `A` in both directions, and it cuts out `χ`.
- A simple design needs a core whose dimension group is simple, such as polynomials positive on a closed
  subinterval of `(0,1)`, while `×x` stays implemented by a corner. So the letter frequencies must be kept away from
  the boundary. No finitely presented mechanism for that is known here.
- Item 3 is the reason frames with `p = I_d` fail (Leavitt, Cuntz–Krieger, Nekrashevych): their index `d[1_B]` is
  scalar, and `isometric-shift-frames-over-uhf-bases-fail-the-k-budget`, item 1, then gives `(d−1)[1_R] = 0`.
  Partial gauge cores of such frames can have non-scalar index.
