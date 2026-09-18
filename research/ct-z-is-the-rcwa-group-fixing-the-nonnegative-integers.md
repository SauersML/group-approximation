---
rg: 2
id: ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers
kind: claim
title: Kohl's class transposition group CT(Z) is exactly the group of residue-class-wise affine permutations of Z that fix the nonnegative integers setwise; this answers Kourovka Problem 17.59 positively
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED** (lane proof, not reviewed). It uses only
`ct-p-z-is-a-one-vertex-k-graph-full-group` (whose cited inputs are listed there) plus
elementary arithmetic. No priority is claimed. The Kourovka Notebook, 21st issue
(2026), still lists 17.59 as unsolved.

## Statement

A permutation `g` of `Z` is *residue-class-wise affine* (RCWA) if for some `m ≥ 1` its
restriction to each residue class mod `m` is affine, `n ↦ (a n + b)/c`. Let
`RCWA^+(Z) = {g ∈ RCWA(Z) : g(N_0) = N_0}`. Then

    CT(Z) = RCWA^+(Z).

Kourovka 17.59 (S. Kohl) asks exactly whether this holds.

## Proof

**(⊆)** A class transposition maps `r1 + t m1` to `r2 + t m2`. With `0 ≤ r_i < m_i`,
the image is nonnegative iff `t ≥ 0` iff the source is nonnegative. So it preserves
`N_0` setwise, and so does every product of class transpositions.

**(⊇)** Let `g ∈ RCWA^+(Z)` be affine on each class `r_i(m)`, `0 ≤ r_i < m`. The
argument has four steps.

1. **Positive slopes.** On `r_i(m)`, `g` is `n ↦ (a_i n + b_i)/c_i` with
   `a_i/c_i ≠ 0`, by injectivity. If `a_i/c_i < 0`, then `g` maps the infinite
   positive tail of `r_i(m)` into the negative integers, contradicting
   `g(N_0) = N_0`. So every slope is positive.
2. **Images are residue classes.** The image of `r_i(m)` is an arithmetic progression
   with integer difference `n_i = a_i m / c_i > 0`, i.e. a residue class `s_i(n_i)`
   with `0 ≤ s_i < n_i`. These classes partition `Z` because `g` is a bijection.
   Since `g` is increasing on `r_i(m)` and consecutive terms go to consecutive terms,
   there is an integer `c` with `g(r_i + t m) = s_i + (t + c) n_i` for all `t`.
3. **No shift.** `g(N_0) = N_0` means nonnegatives go to nonnegatives and negatives to
   negatives, since `g` is a bijection. Take `t = 0`: `r_i ≥ 0` gives
   `s_i + c n_i ≥ 0`, so `c ≥ 0`. Take `t = −1`: `r_i − m < 0` gives
   `s_i + (c − 1) n_i < 0`, so `c ≤ 0`, because `0 ≤ s_i < n_i`. Hence `c = 0`, and
   `g(r_i + t m) = s_i + t n_i`.
4. **Conclusion.** Let `P` be the set of odd primes dividing `m ∏_i n_i`. Then `g` is
   exactly an element of the form described in item 3 of
   `ct-p-z-is-a-one-vertex-k-graph-full-group`. So `g ∈ CT_P(Z) ⊆ CT(Z)`.

## Remarks

- **Pieces.** The same argument shows that every element of `CT(Z)` is "piecewise
  canonical". There are two residue-class partitions of `Z`, and on each piece `g` is
  the unique increasing affine bijection with zero shift.
- **Union.** `CT(Z) = ⋃_{P finite} CT_P(Z)` is a directed union of simple groups of
  type `F_∞` (by the parent node). So `CT(Z)` is locally `F_∞` and simple, which
  recovers Kohl's theorem.
