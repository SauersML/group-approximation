---
rg: 2
id: leavitt-tensor-unit-word-problems-have-one-counting-quantifier
kind: claim
title: Word problems of finitely generated linear groups over Leavitt tensor algebras lie in ∀·Mod_pP (finite fields) or C_=P (Z[1/M]), both bounds are attained, and so PSPACE-hardness needs hosts without finite depth
distinct_from:
  leavitt-square-units-mod-p-complete-word-problem: that is completeness for the square over a prime field; this is the matching upper bound for every tensor power, every L(1,n) factor and every matrix size, the characteristic-zero case, and the barrier for PSPACE.
  leavitt-tensor-unit-word-problem-reduces-to-base: that is an exponential-time bound for units of B ⊗ L over an arbitrary base B; this is a counting-class bound for Leavitt tensor products over finite fields and Z[1/M].
  automaton-tail-full-groups-have-conp-relative-word-problem: that caps piecewise prefix-and-automaton homeomorphism groups at coNP relative to the automaton groups; this caps finite-depth linear hosts at one counting quantifier.
requires:
  - leavitt-square-units-wp-complexity-proof
  - prime-field-leavitt-square-units-mod-p-proof
---

**ESTABLISHED** (route `leavitt-tensor-unit-counting-cap-proof`; lane proof by bh-free-26,
elementary, not independently reviewed).

## Statement

Let `k >= 1`, `n_1, ..., n_k >= 2`, and `A_K = L_K(1,n_1) ⊗_K ... ⊗_K L_K(1,n_k)`. Let
`Γ <= GL_N(A_K)` be finitely generated.

1. **Finite fields.** If `K` is a finite field of characteristic `p`, then
   `WP(Γ) ∈ ∀·Mod_pP`.
2. **Integers.** If `K = Z[1/M]` with `M >= 1` (in particular `K = Z`), then `WP(Γ) ∈ C_=P`.
3. **Both bounds are attained for `k = 2`.**
   - Over any finite field of characteristic `p`, some finitely generated subgroup of
     `(L_K(1,2)^(⊗2))^x` is `∀·Mod_pP`-complete. It contains the prime-field group `Γ_p` of
     `prime-field-leavitt-square-units-mod-p-proof`.
   - The same letters, read over `Z`, generate `Γ_Z <= (L_Z(1,2)^(⊗2))^x` with
     `C_=P`-complete word problem. A pair of circuits `Q_1, Q_2` maps in polynomial time to a
     word `W_(Q_1) W_(Q_2)^(-1) = 1 + a_c (X_1 - X_2) a_d^*`, which is trivial iff
     `#{y : Q_1(x,y)} = #{y : Q_2(x,y)}` for every `x`.

## What this answers

- **No climb from more factors or other Leavitt algebras.** Over `F_q` of characteristic `p`,
  every tensor power, every choice of `L(1,n)` factors and every matrix size stays at
  `∀·Mod_pP`, the level already attained by the square. The counting modulus is the
  characteristic of the coefficients, not the number of Leavitt generators: `L_(F_2)(1,3)`
  still counts mod 2, and mod-3 counting needs `F_3` coefficients. The finitely presented
  simple groups `(L_p^(⊗d))^x / F_p^x` for `d >= 3` (finitely presented and simple by
  `prime-field-leavitt-tensor-powers-have-trivial-k-theory` with
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`) are no harder than `d = 2`.
- **A barrier for PSPACE.** If some finitely generated `Γ` as above had `PSPACE`-hard word
  problem, then `PSPACE ⊆ ∀·Mod_pP` (finite fields) or `PSPACE ⊆ C_=P ⊆ PP`, that is
  `PSPACE = PP` (over `Z[1/M]`). So no Leavitt tensor host of this kind gives a
  `PSPACE`-hard finitely presented simple group without such a collapse.
  - The mechanism is **finite depth**. A word of length `ℓ` is a sum of monomials of
    depth `O(ℓ)`, so one counting quantifier over depth-`O(ℓ)` test points decides it.
  - `PSPACE`-hardness therefore needs elements with no finite depth, such as automaton
    (self-similar) elements. Their sections recur along arbitrarily long paths, which is
    what drives the Wächter--Weiß `PSPACE`-complete automaton group (arXiv:1906.03424).
  - A linear host of that kind would be the unit group of a Nekrashevych (Exel--Pardo)
    algebra of a non-contracting automaton group. Its finite presentation is not known.
- **Boone--Higman predicts a `C_=P`-hard finitely presented simple group.** `Γ_Z` is finitely
  generated with decidable word problem. Every finitely presented simple overgroup of it has
  `C_=P`-hard word problem, and by Toda--Ogiwara (`PH ⊆ BPP^(C_=P)`) that word problem is
  outside PH unless PH collapses. No finitely presented simple overgroup of `Γ_Z` is known.
  Reduction mod `p` maps `Γ_Z` onto `Γ_p`, but no single prime is injective on `Γ_Z`, since
  the counts `X_1 - X_2` can be any integer.
