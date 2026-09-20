---
rg: 2
id: hard-rigid-z2-sfts-via-diagonal-hint-sequences
kind: route
title: Hint the rigid minimal crossing-wire shift with a sequence diagonalized against a tower of the time bound; a fast language algorithm would compute the sequence fast by querying corner macrotiles
target: hard-quantum-rigid-free-minimal-z2-sfts-exist
requires:
  - beta-hinted-crossing-wire-shifts-are-free-minimal-rigid
  - sft-crossed-product-fp-iff-quantum-rigid
---

Lane proof (swarm-0917-w18c-w18c-bh-pull, 2026-09-19). Not independently reviewed. The only non-elementary
input is `beta-hinted-crossing-wire-shifts-are-free-minimal-rigid` (cited as items 1–5). The rest is a
standard time-hierarchy diagonalization.

Let `T` be recursive. Replacing `T` by `n ↦ max_(m <= n) T(m)` only makes the claim stronger, so
assume `T` is nondecreasing.

## 1. The bound to beat

Put `D_k = 2^(2^(2^k))` and `T̂(n) = n^2 + max_(m <= n^2) T(m)`. Both are recursive and nondecreasing,
and `T̂(n) >= C·T(Cn) + Cn^2 + C` once `n >= C`, for every constant `C`. Let
`G(k) = (D_k + T̂(D_k))^k`. It is recursive.

**Domination.** For all constants `C, c >= 1`:
`(C·(L_k^c + T̂(L_k)))^c <= G(k)` for all large `k`, where `L_k <= 3^(C'^(k+1))` for some constant
`C'`, as in item 5(a).

*Proof.* `log log L_k = O(k)` while `log log D_k = 2^k`, so `L_k^c <= D_k` for large `k`. Put
`X = D_k + T̂(D_k)`. Then `L_k^c <= X`, `T̂(L_k) <= T̂(D_k) <= X` (as `T̂` is nondecreasing and
`L_k <= D_k`), and `X >= 2C` for large `k`. So the left side is at most `(2CX)^c <= X^(2c) <= X^k = G(k)`
once `k >= 2c`. ∎

## 2. The diagonal sequence `β`

Enumerate the Turing machines `M_0, M_1, …`. For `j >= 1` let `i(j)` be the number of trailing zeros of
`j` in binary, so each `i` equals `i(j)` for infinitely many `j`. Define

`β_j = 1 − M_(i(j))(j)` if `M_(i(j))` on input `j` halts within `G(j)` steps with output in `{0,1}`,
and `β_j = 0` otherwise (and `β_0 = 0`).

`β` is total recursive (simulate for `G(j)` steps). Let `B` be a machine computing it.

**Lemma.** No machine `M` computes `j ↦ β_j` for all `j` within `G(j)` steps for all large `j`.

*Proof.* Suppose `M` computes `β_j` correctly for every `j` and within `G(j)` steps for all `j >= j_0`.
Then `M = M_i` for some `i`. Take `j >= j_0` with `i(j) = i`. `M_i` halts on `j` within `G(j)` steps with
output `β_j ∈ {0,1}`, so by definition `β_j = 1 − M_i(j) = 1 − β_j`, which is absurd. ∎

## 3. The shift

Let `Ω = Ω_β` for this `β`. By items 2–4 it is free, minimal and quantum rigid over `F_2`, so
`B_Ω = LC(Ω, F_2) ⋊ Z^2` is finitely presented. This is clause 1 of the target, and by
`sft-crossed-product-fp-iff-quantum-rigid` it is equivalent to `D`-quantum rigidity.

## 4. `Ω` is not `T`-decidable

Suppose some machine `A` decides the globally admissible `n × n` patterns of `Ω` in time
`C·T(Cn) + Cn^2 + C <= T̂(n)` for `n >= C`. Consider the machine `R`: on input `j >= 2`, compute
`β_0, …, β_j` in turn. The bit `β_0` is hard-coded. Given `β|(k+1)`, compute `β_(k+1)` for
`k = 0, 1, …, j − 1` as follows.
1. Build `M_b = M(c_k(β|(k+1), β|(k+1)·b))` for `b = 0, 1` by item 5(a), in time `poly(L_k)`. If one
   expansion reports a rejecting zone, output the other `b`.
2. Otherwise run `A` on `M_0`, an `L_k × L_k` pattern. Output `0` if `A` accepts, else `1`.

By the criterion after item 5 of the hinted-shift claim, the output is `β_(k+1)`. So `R` computes
`j ↦ β_j`. Its running time on input `j` is at most, for a constant `c` covering the simulation overhead,
`Σ_(k < j) c·(L_k^c + T̂(L_k)) <= j·c·(L_(j−1)^c + T̂(L_(j−1)))`, since `L` and `T̂` are nondecreasing.
As `j <= L_j`, this is at most `(c·(L_j^c + T̂(L_j)))^2 <= (c·(L_j^(2c) + T̂(L_j)))^(2c)`, which is
`<= G(j)` for all large `j` by the domination in §1. This contradicts
the Lemma. So `Ω` is not `T`-decidable, which is clause 2. ∎

## 5. Remarks

- **No circularity.** `G` and `β` depend only on `T`. The tile set depends on `B`, so its constants `C'`
  (zoom) and `c` (expansion overhead) depend on `β`, but the domination in §1 holds for every
  constant. That is why the diagonal is taken against a triple exponential.
- **Why hardness appears only at double-exponential scale.** Hint bit `k` becomes visible only in
  patterns of size `L_k ≈ 3^(C^k)`. So the hint costs nothing in rigidity, and the tower in `G`
  absorbs the lost scale.
- **Kind of hardness.** The lower bound is infinitely often, on the corner macrotiles, as the target
  needs. An almost-everywhere version would use `almost-everywhere-hard-recursive-sets-exist`; it is not
  needed.
