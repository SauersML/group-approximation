---
rg: 2
id: thompson-f-has-an-amenable-normalish-tail-subgroup
kind: claim
title: Thompson's group F contains an infinitely generated free abelian normalish subgroup made of x_0-translates of one bump accumulating at 0
distinct_from:
  thompson-f-confined-subgroups-fix-finite-sets: that classifies confined subgroups, which contain a germ stabilizer; this subgroup is abelian, contains no germ stabilizer, and is not confined, but every finite intersection of its conjugates contains one of its tails.
  cut-stabilizers-of-el-n-are-locally-finite-normalish: that is a locally finite normalish subgroup of an elementary matrix group over a Cantor ring; this is an abelian normalish subgroup of Thompson's F.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that uses end-rigid subgroups (which contain copies of F) as stabilizers; this uses an abelian subgroup near the end, with the same germ mechanism.
---

**ESTABLISHED.** Let `x_0 ∈ F` be the generator with `x_0(t) = t/2` on `[0,1/2]`. Fix any
nontrivial `h_0 ∈ F` supported in `[1/4,1/2]`, and put `h_n = x_0^n h_0 x_0^(-n)` for `n ≥ 0`.
Let `T = ⟨h_n : n ≥ 0⟩`, and let `T_(≥M) = ⟨h_n : n ≥ M⟩` be its *tails*.

1. `h_n` is supported in `[2^(-n-2), 2^(-n-1)]`, and `h_n(s) = 2^(-n) h_0(2^n s)` there. So the
   `h_n` commute pairwise and `T ≅ ⊕_(n ≥ 0) Z`. In particular `T` is amenable.
2. **Germ rule.** Let `g ∈ F` with `g(t) = 2^k t` on `[0,ε]`. Then `g h_n g^(-1) = h_(n-k)` for every
   `n ≥ N(g)`, where `N(g) = max(k, ⌈log_2(1/ε)⌉)`.
3. **Normalish with tails.** For every finite `g_1, …, g_r ∈ F` there is `M` with
   `T_(≥M) ⊆ ⋂_i g_i T g_i^(-1)`. So `T` is an amenable normalish subgroup of `F`.
4. **Two commensurating steps.** `x_0^(-1) T x_0 ⊇ T` and `x_1^(-1) T x_1 = T`, where `x_1` is the
   standard generator, the identity on `[0,1/2]`.

`T` is not commensurated, since `T / T_(≥1) ≅ Z`. It is not confined either, because it contains no
germ stabilizer `St0_(F')(S)` (`thompson-f-confined-subgroups-fix-finite-sets`).

**Mechanism.** Near the global fixed point `0`, every germ of `F` is a power of the germ of `x_0`, and
`x_0` translates the fundamental domains `[2^(-n-2), 2^(-n-1)]`. Groups with no global fixed point
(Thompson's `T`), or whose germ group at a fixed point is not cyclic, do not get this subgroup by the same
argument.

**Scope.** Elementary, and probably folklore; no novelty is claimed. What it feeds is
`thompson-f-cohomology-certificates-cannot-prove-nonamenability`.

Proof route: `thompson-f-amenable-normalish-tail-subgroup-proof`.
