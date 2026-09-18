---
rg: 2
id: isometric-frames-over-rank-one-bases-fail-the-k-budget-proof
kind: route
title: Stable cancellation makes a block-diagonal frame trivial, which gives a degree-one unit of a matrix ring, and Morita invariance carries the graded dichotomy back
target: isometric-frames-over-rank-one-bases-fail-the-k-budget
requires:
  - isometric-shift-frames-over-uhf-bases-fail-the-k-budget
  - graded-rings-with-degree-one-units-fail-the-k-budget
---

**Input.** **(BC) Bass cancellation**, pinned by gq-referee-b (report 5d2294421) to Weibel, *The K-book*, Ch. I,
Exercise 1.5, p. 4, for general rings, citing Bass V.3.5. In Weibel's `sr` (`sr` of a field is `1`): if `B` has stable
range `d`, then every finitely
generated projective module `P` with `P ⊕ B^a ≅ B^(n+a)` and `n >= d` is free of rank `n`. This is Bass (1964) for
commutative rings, and Vaserstein and Warfield for the noncommutative stable-range condition.

**Setting check.** Under (R1), `[p] ⊗ 1 = r [1_B] ⊗ 1` for a unique rational `r`. With `r = n/m` in lowest terms,
`m[p] - n[1_B]` is torsion in `K_0(B)`, say of order `e`. Replacing `m, n` by `em, en` gives `m[p] = n[1_B]` exactly.
Items 1 and 2 use this, and only the ratio matters.

**Item 1.** Item 1 of `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` holds over any `B`. From
`m[p] = n[1_B]` it gives `(m - n)[1_R] = 0`. Then `rational-k1-detection-forces-infinite-order-unit-class` gives
the conclusion.

**Item 2.**
- With `r = 1`, `m[p] = m[1_B]` in `K_0(B)`. So `(p B^k)^m ⊕ B^a ≅ B^(m+a)` for some `a`.
- Taking `d` copies gives `(p B^k)^(md) ⊕ B^(da) ≅ B^(md + da)`. Since `md >= d`, (BC) makes `(p B^k)^(md)` free of rank
  `j = md`.

**Item 3.**
- Let `P_j = diag(p, ..., p) in M_(jk)(B)`. By item 2 there are `x in M_(jk × j)(B)` and `y in M_(j × jk)(B)` with
  `x y = P_j` and `y x = 1_j`. We may take `x = P_j x` and `y = y P_j`.
- Let `S = diag(s, ..., s)`, a `j × jk` matrix, and `T = diag(t, ..., t)`, a `jk × j` matrix. Then `S T = 1_j` and
  `T S = P_j`.
- Put `U = S x` and `V = y T`, both in `M_j(R)`. Then `U V = S P_j T = (S T)(S T) = 1_j`. Also
  `V U = y P_j x = y x = 1_j`, using `y P_j = y` and `P_j x = x`.
- The entries of `S` lie in `R_1` and those of `x` in `B ⊆ R_0`, so `U in M_j(R_1) = M_j(R)_1`. `Q` embeds in
  `M_j(R)` as scalars.
- The graded node applies to `M_j(R)` and `U`. Either `ker(Q^x -> K_1(M_j(R)))` is not finitely generated, or no
  `E_N(M_j(R))`, `N >= 3`, is finitely presented.
- **Back to `R`.**
  - Under Morita invariance `K_1(M_j(R)) ≅ K_1(R)`, the scalar `λ 1_j` goes to `j[λ]`. So
    `ker(Q^x -> K_1(M_j(R))) = {λ : λ^j in K}`, where `K = ker(Q^x -> K_1(R))`. `Q^x / {±1}` is free abelian, so this
    group is finitely generated if and only if `K` is.
  - `E_N(M_j(R)) = E_(jN)(R)` inside `GL_(jN)(R)` for `N >= 2`. Each generator `e_(ab)(A)` is a product of
    elementary `jN`-matrices. Conversely, an elementary matrix inside a diagonal block is the commutator
    `[e_((a,u),(b,w))(r), e_((b,w),(a,v))(1)]` through a second block `b`, and both factors are block
    elementary matrices.

**Item 4.** Give `B` degree `0`, the `s_i` degree `1` and the `t_i` degree `-1`. Every listed relation is
homogeneous: `t_i s_j - p_ij` has degree `0`; `b s_i - Σ_l s_l (t_l b s_i)` has degree `1`; `t_i b - Σ_l (t_i b s_l) t_l`
has degree `-1`; `s t - 1` has degree `0`. A quotient of a graded ring by a homogeneous ideal is graded.

**Examples.**
- A localization of the PID `Q[N]` is a PID, so its finitely generated projectives are free, `K_0 = Z`, and its
  stable range is at most `2`.
- For `R_L`, `p = t s = I_2`, so `r = 2`.

**Item 3a.** Under (R3), `r = 1` and `m[p] = m[1_B]` in the torsion-free group `K_0(B) = Z[1_B]` give `[p] = [1_B]`.
So `p B^k ≅ B` by (R3), which is item 2 with `j = 1`. The construction of item 3 with `j = 1` gives `x in M_(k×1)(B)`
and `y in M_(1×k)(B)` with `x y = p` and `y x = 1`, and `U = s x in R_1` is a unit of `R` with inverse `y t`. The graded
node applies to `R` directly.
