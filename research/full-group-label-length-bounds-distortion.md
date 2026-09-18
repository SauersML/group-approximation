---
rg: 2
id: full-group-label-length-bounds-distortion
kind: claim
title: Label length is subadditive on a full group, so a subgroup whose labels are locally determined is undistorted in every finitely generated group between it and its full closure
distinct_from:
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that applies this lemma twice (to G*Z inside its horofunction full group, and to a full contracting RSG inside its twisted Brin-Thompson group); this is the general lemma.
---

**ESTABLISHED** (lane proof below, elementary, not independently reviewed; no priority claimed, the
argument is the standard "local label" bound).

## Setting

Let `X` be a compact space, `L <= Homeo(X)` a group, `Q` a group with a finite generating set and word
length `|.|_Q`, and `π : L -> Q` a homomorphism. Call `π` **locally determined** if whenever `l, l' ∈ L`
agree on a nonempty open subset of `X`, then `π(l) = π(l')`. Equivalently: every `l ∈ L` that fixes a
nonempty open set pointwise has `π(l) = 1`.

Let `[[L | X]]` be the full group induced by `L` (BBMZ arXiv:2309.06224, Definition `def:full`): all
homeomorphisms of `X` that locally agree with elements of `L`. Since `X` is compact, each `k ∈ [[L|X]]`
has a finite open cover `U_1, ..., U_m` and labels `l_i ∈ L` with `k = l_i` on `U_i`.

## Statement

Let `K` be a group with a finite generating set, and `K <= [[L | X]]`. Then there is `C` with

    |π(k)|_Q <= C |k|_K    for every k ∈ K ∩ L.

In particular:
1. **(Plain form.)** If `H <= Homeo(X)` is finitely generated and no nontrivial element of `H` fixes a
   nonempty open set pointwise ("`H` acts locally faithfully"), then `H` is undistorted in every
   finitely generated `K` with `H <= K <= [[H | X]]`. (Take `L = Q = H`, `π = id`.)
2. **(Twisted Brin–Thompson form.)** Let `Γ` be finitely generated and act faithfully on a set `S`, and
   let `SV_Γ = [[V ≀_S Γ | C^S]]` (BBMZ, Section `sec:ending`). Then `Γ` (acting by coordinate
   permutations) is undistorted in every finitely generated `K` with `Γ <= K <= SV_Γ`, in particular in
   `SV_Γ` whenever that group is finitely generated.
   For `K = SV_Γ` this is Belk–Zaremsky, arXiv:2001.04579, Theorem 1.2 (`thm:quasi-retracts`), proved there
   by an explicit quasi-retraction `SV_Γ -> Γ`. The label-length proof below is different and also covers
   intermediate `K`, but the `K = SV_Γ` case is theirs.

## Proof

For `k ∈ [[L|X]]` put `λ(k) = min max_i |π(l_i)|_Q`, the minimum over finite open covers `{U_i}` of `X`
with labels `l_i ∈ L`, `k|_{U_i} = l_i|_{U_i}`.

- **Subadditive.** If `k = l_i` on `U_i` and `k' = m_j` on `W_j`, then `k k' = l_i m_j` on the open sets
  `W_j ∩ k'^{-1}(U_i)`, which cover `X`, and `|π(l_i m_j)| <= |π(l_i)| + |π(m_j)|`. So
  `λ(k k') <= λ(k) + λ(k')`. Also `k^{-1} = l_i^{-1}` on `k(U_i)`, so `λ(k^{-1}) = λ(k)`.
- **Upper bound.** With `A = max λ(s)` over the finite generating set of `K` and its inverses,
  `λ(k) <= A |k|_K`.
- **Lower bound on `K ∩ L`.** If `k ∈ L` and `k = l_i` on a nonempty `U_i`, then local determination
  gives `π(l_i) = π(k)`. Every cover has a nonempty member, so `λ(k) >= |π(k)|_Q`.

So `|π(k)|_Q <= λ(k) <= A |k|_K`.

**Form 1** is the case `L = Q = H`, `π = id`: local faithfulness is exactly local determination.

**Form 2.** Take `L = V ≀_S Γ` acting on `C^S` by `((v_s), γ) · x = (v_s(x_{γ^{-1}s}))_s`, and `π` the
projection to `Γ`. It remains to check local determination: suppose `l = ((v_s), γ)` fixes a nonempty
open set pointwise. Shrink it to a basic open set `U = ∏_{s ∈ F} U_s × C^{S∖F}` with `F` finite and each
`U_s` nonempty open in `C`. If `γ^{-1}s = a ≠ s` for some `s`, pick `x ∈ U` and change only its
`s`-coordinate inside `U_s` (possible, since `C` has no isolated points). Then `(l·x)_s = v_s(x_a)` is
unchanged, while `x_s` changed, so `l` cannot fix both points. Hence `γ^{-1}s = s` for every `s`, and
`γ = 1` because `Γ` acts faithfully on `S`. Every element of `Γ ≤ SV_Γ` lies in `L`, so the statement
applies. ∎
