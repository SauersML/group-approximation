---
rg: 2
id: thompson-t-mixed-identity-decision-procedure-proof
kind: route
title: Nontriviality shows on a dyadic trajectory, finite order-preserving partial maps extend, and each trajectory type is a Z[1/2]-feasibility question
target: thompson-t-mixed-identity-problem-is-decidable
requires: []
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

Self-contained. Products compose right to left: `(gh)(p) = g(h(p))`.

**Lemma L1 (dyadic intervals).** For dyadic `a < b` and `c < d` there is an
increasing piecewise-linear homeomorphism `λ : [a,b] -> [c,d]` with finitely
many dyadic breakpoints, slopes powers of 2, and `λ(Z[1/2] ∩ [a,b]) = Z[1/2] ∩ [c,d]`.

*Proof.* Choose `M` with `2^M a, 2^M b in Z`. Then `[a,b]` is a union of
`2^M (b-a)` consecutive intervals of length `2^-M`, and likewise `[c,d]` for
some `M'`. Halving one piece raises the count by one and keeps every piece a
dyadic interval of length a power of 2. So both sides split into the same number
of consecutive pieces `I_1, ..., I_N` and `J_1, ..., J_N`. Map `I_i` affinely
onto `J_i`. The map is `t -> 2^e t + δ` with `δ` dyadic, so it sends dyadics
onto dyadics. `∎`

**Lemma L2 (extension).**
- **(F)** If `u_1 < ... < u_r` and `v_1 < ... < v_r` are dyadic points of `(0,1)`,
  some `f in F` has `f(u_i) = v_i` for all `i`.
- **(T)** Let `P` be a finite partial injection of `D` that preserves cyclic
  order: every three distinct domain points have the same orientation as their
  images. Then some `g in T` extends `P`.

*Proof.* (F): with `u_0 = v_0 = 0` and `u_(r+1) = v_(r+1) = 1`, apply L1 on each
`[u_i, u_(i+1)] -> [v_i, v_(i+1)]` and glue.

(T): if `P` is empty take `g = 1`. Otherwise fix `(u_1, v_1) in P` and the
rotation `ρ(t) = t + v_1 - u_1`, which lies in `T`.
- `Q = P ρ^-1` preserves cyclic order and fixes `v_1`.
- Cut at `v_1` with `τ(t) = t - v_1 mod 1`, identifying `S^1 ∖ {v_1}` with `(0,1)`.
- For domain points `s < s'` of `τ Q τ^-1` in `(0,1)`, the triple `(0, s, s')` is
  positive. Its image `(0, τQτ^-1(s), τQτ^-1(s'))` is then positive, so
  `τQτ^-1(s) < τQτ^-1(s')`.
- (F) extends this increasing partial injection to `f in F`.
- `h = τ^-1 f τ`, fixing `v_1`, lies in `T`, and `g = h ρ` extends `P`. `∎`

**Lemma L3 (dyadic witnesses).** For `x in G^k`, `w(x)` lies in `G`. If it is
nontrivial it moves an open interval, hence some point of `D` (for `T`) or of
`Z[1/2] ∩ (0,1)` (for `F`).

**Trajectories.** Write `w` as letters `l_1 l_2 ... l_L`. Each letter is a
constant `c in G`, given by a word in the generators, or a variable `x_m^(±1)`.
Given `x in G^k` and a witness point `p`:
- put `t_L = p` and `t_(i-1) = l_i(t_i)`, so `t_0 = w(x)(p)`;
- for each `m`, let `P_m` collect `(t_i, t_(i-1))` when `l_i = x_m`, and
  `(t_(i-1), t_i)` when `l_i = x_m^-1`.

`P_m` is a restriction of `x_m`. So it is the graph of a partial injection
preserving order (for `F`) or cyclic order (for `T`).

A *configuration* is a sequence `t_0, ..., t_L` of points of `D` (for `T`), or
of `Z[1/2] ∩ (0,1)` (for `F`), such that:
- (i) `t_(i-1) = c(t_i)` whenever `l_i = c` is a constant;
- (ii) each `P_m` is the graph of a partial injection preserving the (cyclic)
  order;
- (iii) `t_0 != t_L`.

By L2, each `P_m` extends to some `x_m in G`, and then `w(x)(t_L) = t_0 != t_L`.
With L3:

```text
w ∉ J_k(G)   iff   a configuration exists.                              (DT1)
```

**Types.** Represent `D` by `[0,1)`. Each constant `c` is computable from its
word as finitely many affine pieces `c(t) = 2^e t + δ` on half-open intervals
`[β, β')` with dyadic data. For `T`, subdivide at the dyadic preimages of `0`,
so that no piece wraps around. A *type* consists of:
- for each constant letter `l_i`, the piece containing `t_i`;
- a weak linear order, ties allowed, on the symbols `t_0, ..., t_L`.

There are finitely many types.

The weak order alone decides (ii) and (iii):
- functionality and injectivity of `P_m` are statements about ties;
- the orientation of a triple in `[0,1)` is the parity of the cyclic arrangement,
  computable from the order.

A type passing these checks determines the linear system

```text
t_(i-1) = 2^e t_i + δ  and  β <= t_i < β'    (constant letters, chosen pieces)
t_i = t_j  or  t_i < t_j                      (the weak order)
0 <= t_i < 1  (T)        0 < t_i < 1  (F)                                 (DT2)
```

Its solutions in `Z[1/2]^(L+1)` are exactly the configurations of that type.

**Lemma L4 (`Z[1/2]`-feasibility).** For finitely many linear equations and
inequalities, strict or not, with coefficients in `Z[1/2]`, it is decidable
whether a solution in `Z[1/2]^N` exists.

*Proof.* Split every non-strict inequality into an equality or a strict one.
This gives finitely many systems `E ∪ S`, with equations `E` and strict
inequalities `S`. Clearing powers of 2, write `E` as `M t = b` with `M, b`
integral.
- **Equations.** Compute the Smith normal form `M = U Δ V`, with `U, V`
  unimodular integer matrices and `Δ` diagonal. `s = V t` is a bijection of
  `Z[1/2]^N`, and `E` becomes `Δ s = U^-1 b`. A row with `Δ_ii = d != 0` is
  solvable in `Z[1/2]` iff the odd part of `d` divides `(U^-1 b)_i`. A row with
  `Δ_ii = 0` needs `(U^-1 b)_i = 0`.
- **Density.** If `t_0 in Z[1/2]^N` solves `E`, the real solutions are
  `t_0 + ker_R M`. This kernel has a basis `z_1, ..., z_r` of integer vectors. As
  `Z[1/2]` is dense in `R`, the points `t_0 + Σ μ_j z_j` with `μ_j in Z[1/2]` are
  dense among the real solutions of `E`.
- **Strict part.** The real solutions of `E ∪ S` are relatively open in that
  affine space. So `E ∪ S` has a `Z[1/2]`-solution iff `E` has one and `E ∪ S`
  has a real solution. The latter is linear programming over `Q`, decided by
  Fourier--Motzkin elimination. `∎`

**The algorithm.**
1. Enumerate the types.
2. Discard those failing (ii) or (iii).
3. Decide (DT2) for each remaining type by L4.

By (DT1), `w ∉ J_k(G)` iff some type succeeds. `∎`

**Remarks.**
- Ties are part of the type, so a forced equation such as `t = 4t - 1`, with no
  dyadic solution, is rejected by the Smith normal form test, not by real
  feasibility.
- Reducedness of `w` is not used, and each variable contributes its own `P_m`,
  so every `k` is handled at once.
- The procedure is uniform in `w`: one algorithm serves all words.
