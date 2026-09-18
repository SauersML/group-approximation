---
rg: 2
id: ct-z-north-south-element-has-no-finite-cycles
kind: claim
title: An explicit product of five class transpositions has no finite cycles on Z and permutes no nontrivial partition of Z into residue classes
---

**ESTABLISHED** (lane proof, not reviewed). Elementary and self-contained. No
priority is claimed.

## Statement

Let `ψ = τ_{0(4),2(16)} · τ_{3(4),14(16)} · τ_{1(4),6(16)} · τ_{1(4),10(16)} · τ_{1(4),2(4)}`,
composed right to left, so `τ_{1(4),2(4)}` acts first. Then `ψ ∈ CT(Z)`, and
`ψ` lies in `CT_∅(Z)` since all moduli are powers of 2. It is the rcwa permutation

    ψ(n) = 4n + 2     if n ≢ 1 (mod 4),
    ψ(n) = n − 3      if n ≡ 9 (mod 16),
    ψ(n) = (n − 1)/4  if n ≡ 1, 5, 13 (mod 16).

1. `ψ` has no finite cycles on `Z`.
2. `ψ` permutes no partition of `Z` into at least two residue classes.
3. For every residue class `D = j(m)`, put `κ(x) = j + m x`. The conjugate
   `ψ_D = κ ψ κ^{-1}` on `D`, extended by the identity off `D`, is the product of the
   five class transpositions `τ_{κ(A),κ(B)}`, where `τ_{A,B}` runs over the factors of
   `ψ`. It has no finite cycles on `D`.

   Here `κ(r(m')) = (j + m r)(m m')`, and `κ` conjugates canonical class maps to
   canonical class maps.

## Proof

**The word equals the formula.**
- **First factor.** `τ_{1(4),2(4)}` swaps `1 + 4k` and `2 + 4k`. It maps the partition
  `{0(4), 2(4), 3(4), 1(16), 5(16), 9(16), 13(16)}` class by class, canonically, onto
  `{0(4), 1(4), 3(4), 2(16), 6(16), 10(16), 14(16)}`. It fixes `0(4)` and `3(4)`, and
  sends `2(4) → 1(4)`, `1(16) → 2(16)`, `5(16) → 6(16)`, `9(16) → 10(16)` and
  `13(16) → 14(16)`.
- **Remaining factors.** These only permute classes of the second partition:
  - the swaps `0(4) ↔ 2(16)` and `3(4) ↔ 14(16)`;
  - the 3-cycle `1(4) → 10(16) → 6(16) → 1(4)`, which is `τ_{1(4),6(16)} τ_{1(4),10(16)}`.
- **Composite.** A composite of canonical maps is canonical. So the word maps
  - `0(4) → 2(16)`, `2(4) → 10(16)` and `3(4) → 14(16)`, all by `4n + 2`;
  - `1(16) → 0(4)`, `5(16) → 1(4)` and `13(16) → 3(4)`, all by `(n − 1)/4`;
  - `9(16) → 6(16)`, by `n − 3`.
  This is the formula. Spot checks: `0 ↦ 2`, `1 ↦ 0`, `2 ↦ 10`, `3 ↦ 14`, `5 ↦ 1`,
  `6 ↦ 26`, `9 ↦ 6`, `13 ↦ 3`, `17 ↦ 4`, `−1 ↦ −2`.

**1.** Let `n ∈ Z`.
- If `n ≢ 1 (mod 4)`, then `ψ(n) = 4n + 2 ∈ 2(4)`.
- On `1(4)`:
  - `1(16)` goes to `0(4)`;
  - `13(16)` goes to `3(4)`;
  - `9(16)` goes to `6(16) ⊆ 2(4)`;
  - `5(16)` goes back into `1(4)`, with `|(n − 1)/4| < |n|`, and the value stays
    nonzero because `1 ∉ 5(16)`. So only finitely many `5(16)` steps occur in a row.
- Hence every orbit enters `2(4)`.
- On `2(4)` we have `ψ(n) = 4n + 2 ∈ 2(4)` and `|4n + 2| > |n|`, since `|n| ≥ 2`.
  So `|ψ^i(n)|` eventually increases strictly, the forward orbit is infinite, and no
  integer is periodic.

**2.** Extend `ψ` to a homeomorphism `ψ̂` of `Z_2` by the same formulas. Put
`a = −2/3 ∈ 10 + 16Z_2` and `r = −1/3 ∈ 5 + 16Z_2`.

- **Forward orbits converge to `a`.** On `2 + 4Z_2` we have
  `ψ̂(x) − a = 4(x − a)`, so `ψ̂` contracts toward `a` and preserves that ball.
  Every `x ≠ r` reaches `2 + 4Z_2`, by the argument of 1. On `5 + 16Z_2`,
  `ψ̂(x) − r = (x − r)/4`, so an `x ≠ r` leaves `5 + 16Z_2` after finitely many steps.
- **Backward orbits converge to `r`.** The inverse is:
  - `ψ̂^{-1}(y) = 4y + 1` off `2 + 4Z_2`;
  - `y + 3` on `6 + 16Z_2`;
  - `(y − 2)/4` on `2 + 16Z_2`, `10 + 16Z_2` and `14 + 16Z_2`.

  By the symmetric argument, every `y ≠ a` has `ψ̂^{-i}(y) → r`.
- **Each class of an invariant partition has odd modulus.** Suppose `ψ` permutes a
  partition `𝒫` of `Z` into `N ≥ 2` residue classes, and put `M = N!`. Then
  `ψ^M(C) = C` for each `C = c(2^e q) ∈ 𝒫`, with `q` odd.
  - The closure of `C` in `Z_2` is the ball `c + 2^e Z_2`, and it is
    `ψ̂^M`-invariant.
  - It contains a point other than `r`, so it contains `a`. It contains a point other
    than `a`, so it contains `r`.
  - Since `a ≡ 2` and `r ≡ 1 (mod 4)`, we get `e = 0`. So every class of `𝒫` has odd
    modulus.
- **Odd moduli are impossible.** Let `C = c(q)` and `ψ(C) = D = d(q')` in `𝒫`.
  - Each piece domain of `ψ` has modulus dividing 16. So by the Chinese remainder
    theorem it contains some `n ∈ C`, and then also `n + 16q`.
  - Comparing images gives `q' | 16λq` with `λ ∈ {4, 1, 1/4}`, so `q' | q`. The same
    argument for `ψ^{-1}` gives `q | q'`. Hence `q' = q`.
  - Reading the three formulas mod `q`:
    - `4c + 2 ≡ d`;
    - `c − 3 ≡ d`;
    - `4d ≡ c − 1`.
  - The first two give `3c ≡ −5`. The first and third give `15c ≡ −9`, and so
    `−25 ≡ −9`, i.e. `q | 16`.
  - So `q = 1` and `C = Z`, contradicting `N ≥ 2`.

**3.** On `D`, `ψ_D` is conjugate to `ψ` by the bijection `κ : Z → D`.

## Use

This is the garbage filler in `ct-z-finite-cycle-problems-are-undecidable` (Kourovka
21.74(c)). By 2, `ψ` is an explicit no-instance of Kourovka 21.74(a).
