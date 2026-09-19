---
rg: 2
id: leavitt-cone-half-carries-rigid-compression-defect
kind: claim
title: The Cuntz-cone half of St_20 of the binary Leavitt algebra carries a Kazhdan compression pair with a nontrivial rigid compression defect in the whole group
distinct_from:
  cone-half-compression-defects-force-head-bound: that proves this statement implies the cone head bound (QC), and that only such half configurations can enter an exact compression argument; this is the open algebraic statement itself, with the constraints its witnesses must meet.
  compression-defects-die-in-rigid-targets: that defines the intrinsic defect D_G(L) and kills it in finite and linear targets; this asks for a nonzero defect in the non-linear group Delta, with the Kazhdan group and compressor restricted to one residually finite half.
  openai-leavitt-unit-nonsofic: that uses a Kun-Thom configuration in the unit group whose compressors mix s and t; this asks for the same kind of configuration with compressor and Kazhdan group inside the Cuntz cone.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that asks which approximable groups kill rigid defects; this asks whether one specific defect exists, with one-sided support.
artifacts:
  - research/cone-half-compression-defects-force-head-bound.md
  - research/depth-monotone-leavitt-subalgebras-are-stably-finite.md
---

**OPEN.** Setting and notation are those of `cone-half-compression-defects-force-head-bound`: `R = L_(F_2)(1,2)`,
`Delta = GL_20(R)`, `Delta_+ = E_20(R_+) <= Delta` with `R_+ = <s_1, s_2, q>`, and `M = M_20(R)`.

**(HEC).** There exist:
- `L <= Delta_+` with property (T);
- `u ∈ Delta_+` with `u L u^-1 <= L`;
- `c ∈ C_Delta(L)` and `l ∈ L` with `[u c u^-1, l] ≠ 1`.

Equivalently, `C_Delta(u L u^-1) ≠ C_Delta(L)`. The inclusion `⊇` always holds, and the left side equals
`u C_Delta(L) u^-1`.

**Why it matters.** By `cone-half-compression-defects-force-head-bound`:
- (HEC) implies `(QC)` with a linear modulus;
- (HEC) makes non-hyperlinearity of `Delta` equivalent to `(HR)`;
- no other compression configuration can be used exactly in genuine representations of the cone cover.

## Constraints on witnesses (all proved here)

**(C0) The compression must be strict.** If `u L u^-1 = L`, then `C_Delta(u L u^-1) = C_Delta(L)`.

**(C1) The compressor has infinite order.** If `u^m = 1` then `L = u^m L u^-m <= u L u^-1 <= L`, which is (C0).

**(C2) The compression is profinitely invisible in the half.**
- Let `pi` be any finite quotient of `Delta_+`. Then `pi(u) pi(L) pi(u)^-1 <= pi(L)` is an inclusion of finite sets of
  equal size, so `pi(u L u^-1) = pi(L)`.
- So `L` lies in the profinite closure of `u L u^-1` in `Delta_+`, and `u L u^-1` is a proper, non-separable
  subgroup of the residually finite group `Delta_+` (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`, Statement 1).
- The same holds with `pi` running over the congruence quotients `GL_20(R_+/J)`, `J` a finite-index two-sided ideal.

**(C3) The centralizing element is outside every residually finite overgroup.**
- Let `H = <L, u, c>`. Apply (HT) of `cone-half-compression-defects-force-head-bound` to `Lambda = H`, where
  `[s, c] = 1` exactly. It shows that every finite-dimensional unitary representation of `H` kills
  `[u c u^-1, l]`.
- Finite groups embed unitarily, so `H` is not residually finite, and in particular `c ∉ Delta_+`.
- The linear case is `compression-defects-die-in-rigid-targets`.

**(C4) Commutants of corner type are rigid.** Let `A' = C_M(L)` be the commutant of `L` in the matrix ring.
Suppose

```text
A' = B + e M e,     e = e^2 ∈ M_20(R_+),  e ≠ 0,  B ⊆ (1-e) M (1-e) a finite-dimensional unital subalgebra.
```

Then `u A' u^-1 = A'` for every `u ∈ GL_20(R_+)` with `u L u^-1 <= L`, so (HEC) fails for `L`.

*Proof.*
1. Put `f = u e u^-1`. Since `u L u^-1 <= L`, we have `A' ⊆ (u L u^-1)' = u A' u^-1 = uBu^-1 + f M f`, a direct
   product of algebras supported on the orthogonal corners `1 - f` and `f`.
2. Compressing to the corner `1 - f` restricts to an algebra map `eMe -> uBu^-1`.
   - `M` is simple because `R` is simple, so its nonzero corner `eMe` is simple.
   - `eMe` is infinite-dimensional, while `uBu^-1` is finite-dimensional. So the kernel is nonzero, hence all of
     `eMe`.
   - Therefore `eMe ⊆ fMf`, and in particular `e = f e = e f`, that is, `e <= f`.
3. Put `g = u^-1 e u <= e`, and let `x = u g` and `y = g u^-1`. These lie in the corner ring
   `e M_20(R_+) e`, with `xy = e` and `yx = g`.
   - `M_20(R_+)` is directly finite: `R_+ = span{s_μ, s_μ s_1 t_1}` lies in the stably finite
     `R^ω_≥ = span{s_μ t_ν : ω(μ) >= ω(ν)}` of `depth-monotone-leavitt-subalgebras-are-stably-finite` (with
     `a = b = 1`).
   - Corners of directly finite rings are directly finite, since `(x + 1 - e)(y + 1 - e) = 1`.
   - Hence `g = e`, so `f = e`.
4. Then `B` and `uBu^-1` are unital subalgebras of `(1-e)M(1-e)` of equal finite dimension, with `B ⊆ uBu^-1`. So
   they are equal, and `u A' u^-1 = A'`.
5. Group centralizers follow: `C_Delta(L) = A' ∩ Delta`.  ∎

*Instances.*
- Take `L = E_k(S)` in a diagonal block, with `3 <= k <= 19` and `S` a finitely generated unital subring of `R_+`
  containing `s_1` and `s_2`. Then `L` is Kazhdan (Ershov–Jaikin-Zapirain) and `A' = F_2 E + (1-E)M(1-E)`, where `E`
  is the block idempotent.
- The derivation of this commutant has three parts:
  - `X ∈ A'` commutes with the block matrix units, so it is block diagonal with scalar `a` on the block.
  - `a` commutes with `S`, so `a ∈ C_R(s_1, s_2)`.
  - `C_R(s_1, s_2) = F_2`: if `x s_i = s_i x` then `t_i x = sum_j t_i s_j x t_j = x t_i`, so `x` is central. The
    center of the simple graded ring `R` is a graded field. A nonzero homogeneous central element of degree `d ≠ 0`
    would make `1 + x` invertible in `Z(R)`, and comparing top degrees in `(1+x)y = 1` rules this out. So `Z(R)` is
    concentrated in degree 0. There it lies in the center of the matricial `R_0 = ∪ M_(2^n)(F_2)`, which is `F_2`.
- So every block or corner compression of `E_k` of the cone ring dies at step 3, the invariant being **stable
  finiteness of `M_20(R_+)`**. The same `L` compressed by the mixed Kun–Thom unit `s_11 t_1 + s_12 t_21 + s_2 t_22`
  would survive step 3. That compressor is not in `Delta_+`.

## Survivors and next test

A witness must have all of the following:
- an infinite-order compressor in `Delta_+`;
- a strict, profinitely dense compression of a Kazhdan subgroup of `Delta_+`;
- a centralizing element outside every residually finite subgroup containing `L` and `u`;
- a commutant `C_M(L)` whose infinite-dimensional part is **not** a single corner `eMe` with `e` over `R_+`.

The last condition points to Kazhdan subgroups whose coefficient ring has a large centralizer in `R`. The smallest
case is `L = E_3(F_2[s_1])` in a block, whose commutant contains `C_R(s_1) E ⊋ F_2 E`. The next step is to decide
whether some `u ∈ Delta_+` compresses `E_3(F_2[s_1])`, or a Kazhdan group containing it, strictly into itself.
