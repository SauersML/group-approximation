---
rg: 2
id: leavitt-square-units-have-conp-parity-p-complete-word-problem
kind: claim
title: The word problem of the finitely presented simple group (L ⊗ L)^x is coNP^⊕P-complete, so it is not in coNP unless the polynomial hierarchy collapses
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups beyond every recursive time bound; this pins one finitely presented simple group at the class coNP^⊕P, strictly above the coNP-complete Brin--Thompson groups unless the polynomial hierarchy collapses, and it does not give unbounded complexity.
  leavitt-tensor-unit-word-problem-reduces-to-base: that is an exponential-time upper bound for word problems of units of B ⊗ L; this is a matching lower and upper bound, coNP^⊕P-completeness, for (L ⊗ L)^x.
  leavitt-square-unit-group-is-fp-simple-and-acyclic: that supplies finite presentation and simplicity of the host; this is the complexity of its word problem.
requires:
  - leavitt-square-unit-group-is-fp-simple-and-acyclic
---

**ESTABLISHED** (route `leavitt-square-units-wp-complexity-proof`; lane proof by bh-free-26,
elementary, not independently reviewed). No priority is claimed. A bounded arXiv search
(2026-09-18) found no complexity result for word problems of Leavitt or Cuntz unit groups;
Birget's papers treat Thompson groups and their monoids.

## Statement

Let `L = L_(F_2)(1,2)`, `A = L ⊗_(F_2) L`, and `H = A^x`. Write
`coNP^⊕P = ∀·⊕P`: the languages `{w : for all x, #{y : R(w,x,y)} is even}` with `R`
polynomial-time and `|x|, |y|` polynomial in `|w|`.

1. **Hardness (unconditional).** There is an explicit finite set `Λ` of units of `A` such that
   the word problem of `Γ = <Λ>` is `coNP^⊕P`-hard under polynomial-time many-one reductions.
   Given a Boolean circuit `R(x,y)` of size `s`, a word `W_R` over `Λ` of length `O(s^3)` is
   computed in polynomial time with

   `W_R = 1  ⇔  for every x, #{y : R(x,y) = 1} is even.`

   With `y` empty this is coNP-hard (circuit unsatisfiability); with `x` empty it is
   `⊕P`-hard.
2. **Upper bound (unconditional).** Every finitely generated subgroup of `A^x` has word problem
   in `coNP^⊕P`.
3. **The host.** `H` is finitely presented and simple by
   `leavitt-square-unit-group-is-fp-simple-and-acyclic` (conditional there on imported criteria
   of Khanh and Ara--Cortiñas). Since `Γ ≤ H`, **the word problem of the finitely presented
   simple group `H` is `coNP^⊕P`-complete**, for every finite generating set.
4. **Consequence.** If `WP(H)` were in coNP, then `⊕P ⊆ coNP`, and Toda's theorem
   (`PH ⊆ BPP^⊕P`) with the relativized Sipser--Gács--Lautemann theorem gives
   `PH ⊆ BPP^NP ⊆ Σ_3^p`, a collapse of the polynomial hierarchy. Also `PH ⊆ BPP^(WP(H))`.

## Why it matters

The hardest finitely presented simple groups previously classified here are the
Brin--Thompson groups `nV`, whose word problem is coNP-complete (Birget, arXiv:1902.03852,
quoted in `fp-simple-groups-with-arbitrarily-complex-word-problem`). Under the standard
assumption that the polynomial hierarchy is infinite, `H` is strictly harder. That is a
concrete step on that root: the first finitely presented simple group whose word problem
provably escapes coNP modulo a standard hypothesis. It does not settle the root, since
`coNP^⊕P` is one fixed class.

## Mechanism (see the route)

- **Superposition letters.** `τ = s_0 + s_1` ("push a digit, both values") and
  `σ = t_0 + t_1` ("pop a digit and add") are not units, but explicit *slot units* conjugate a
  transvection `1 + a_c X a_e^*` into `1 + a_c X B a_e^*` or `1 + a_e A X a_d^*` for these and
  other letters. One commutator of two such transvections gives `1 + a_c (L R) a_d^*` for a
  product `L` of surjective letters and a product `R` of injective letters, with word length
  linear in the number of letters.
- **Circuits.** The baker unit `b_0 a_0^* + b_1 a_1^*` moves digits between the two tensor
  factors, so a gate on digit `r` costs `O(r)` letters (in one factor it would cost `2^r`).
  Bennett's reversible compute-copy-uncompute then realizes `b := b ⊕ R(x,y)` as a
  polynomial-length word.
- **Counting.** `σ^q t_1 (t_0)^K P_R (s_0)^(K+1) τ^q` equals multiplication by
  `x ↦ ⊕_y R(x,y)`: the pushes prepare all `y` in superposition, the circuit computes, and the
  pops keep the accepting branches and add them mod 2.
- **Upper bound.** An element of depth `D` vanishes iff it kills every function
  `1_[αε] ⊗ 1_[βη]` with `|α| = |β| = D` and a fixed non-self-overlapping `ε, η`. Each value
  `(W f)(z)` is a parity of polynomially checkable monomial paths.

## Scope

- The same argument works in `L^(⊗d)`, `d >= 2`. In `L` itself, gates at depth `r` cost `2^r`
  and the proof does not apply; the complexity of `WP(L^x)` is not decided here.
- Over `F_p`, parities become counts mod `p` (`coNP^(Mod_p P)` for finitely generated subgroups
  of `(L_(F_p)(1,2)^(⊗2))^x`). Finite presentation and simplicity of those hosts are not
  claimed.
