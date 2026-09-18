---
rg: 2
id: analytic-codings-make-contracting-recursions-analytic
kind: claim
title: In a real-analytic tree coding of the Cantor space, a piecewise-analytic map satisfying a contracting recursion y∘g_u = g_v∘y has no breakpoint away from the fixed point of g_u
distinct_from:
  piecewise-analytic-circle-square-conjugate-has-parabolic-ends: that constrains elements conjugate to their squares through their derivatives at fixed points; this constrains self-similar elements through the position of their breakpoints, and needs no conjugacy relation inside the group.
  fp-piecewise-projective-groups-rigidity-criterion: that locates support endpoints in finitely presented piecewise projective groups through a specialization argument; this is an elementary statement about one element and one recursion, with no finite presentation.
---

**ESTABLISHED** through `analytic-codings-make-contracting-recursions-analytic-proof` (lane
proof, elementary, not independently reviewed; no priority claimed, since this is breakpoint
bookkeeping of the kind used for PL and projective Thompson-like groups).

## Setting

Let `C_n = {0, …, n−1}^ω` and let `J = [a, b] ⊂ R` be a nondegenerate compact interval. An
**analytic tree coding** is a continuous surjection `ψ : C_n → J` together with maps
`g_0, …, g_(n−1)`, each a real-analytic diffeomorphism from an open neighbourhood of `J` onto its
image, such that

`ψ(iζ) = g_i(ψ(ζ))` for every digit `i` and every `ζ ∈ C_n`.

Write `g_s = g_(s_1) ∘ ⋯ ∘ g_(s_k)` for a word `s`, so `ψ(sζ) = g_s(ψ(ζ))`. PL codings (affine
`g_i`), the Stern–Brocot and Farey codings of Lodha–Moore (`g_i ∈ PSL_2(Z)`), and every digit
recoding of these through a complete prefix code are analytic tree codings.

A homeomorphism `Y` of `J` is **piecewise analytic** if there are `a = t_0 < ⋯ < t_m = b` such
that `Y` is real-analytic on a neighbourhood of each `[t_(i−1), t_i]`. Its **breakpoints** are the
interior points of `J` at which `Y` is not analytic.

## Statement

Let `Y` be a piecewise-analytic homeomorphism of `J`, and let `u ≠ ∅` and `v` be words with

`Y ∘ g_u = g_v ∘ Y` on `J`.

1. `g_u` has exactly one fixed point `p` in `J`, namely `ψ(u^∞)`.
2. Every breakpoint of `Y` equals `p`. So `Y` is analytic on each of `[a, p]` and `[p, b]`.

Continuity of `ψ` alone makes `diam g_(u^k)(J) → 0`, so no contraction hypothesis is needed.

## Corollary (a finitary branch pins the map)

Suppose in addition that `Y ∘ g_w = g_z` on `J` for words `w, z` (a *finitary branch*: `Y` is a
prefix replacement on the cone `w`). Let `S` be `J` if `g_w(J)` contains `p` in its interior,
and otherwise the side, `[a,p]` or `[p,b]`, that contains `g_w(J)`. Let `Φ` be the analytic
continuation to `S` of `g_z ∘ g_w^(−1)` from `g_w(J)`. Then:

- `Y = Φ` on `S`, and
- `Φ ∘ g_u = g_v ∘ Φ` on `S ∩ g_u^(−1)(S)`.

The second item is an identity between explicit analytic maps built from the coding alone, so it can
be checked directly. In words: **in an analytic host, the finitary branches and the recursive
branches of one self-similar element must be analytic continuations of each other.**
`n-adic-lodha-moore-groups-have-no-analytic-tree-coding` is the case `u = 00`, `v = 0`, `w = 0k`,
`z = k`.

## Lesson for general BH

Piecewise-analytic hosts (Monod's `H(R)`, `PA(S^1)`, the Lodha–Moore groups) are rigid in a way
Thompson-like hosts are not. A contracting recursion pushes every breakpoint to the recursion's
fixed point, so a self-similar generator is essentially one analytic map. Such hosts can absorb only
self-similar structure whose finitary and recursive branches continue each other analytically.
It is a close cousin of the fixed-point germ rigidity that excludes Higman's group and the
Baumslag–Gersten group from them. It is why a general Boone–Higman host has to be of prefix-replacement (Cantor) type, where germs do not
propagate along recursions.
