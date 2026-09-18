---
rg: 2
id: leavitt-square-units-mod-p-complete-word-problem
kind: claim
title: For every prime p the finitely presented simple group (L_(F_p)(1,2) ⊗ L_(F_p)(1,2))^x / F_p^x has word problem complete for ∀·Mod_pP
distinct_from:
  leavitt-square-units-have-conp-parity-p-complete-word-problem: that is the case p = 2, proved there with a characteristic-two slot unit; this is every prime p, with a characteristic-free slot unit and the projective quotient needed when p is odd.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that supplies finite presentation and simplicity of the hosts; this is the complexity of their word problems.
  leavitt-tensor-unit-word-problems-have-one-counting-quantifier: that is the upper bound for all Leavitt tensor hosts and the barrier it puts on PSPACE; this is completeness for the square over a prime field.
requires:
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - prime-field-leavitt-tensor-powers-have-trivial-k-theory
  - leavitt-square-units-wp-complexity-proof
---

**ESTABLISHED** (route `prime-field-leavitt-square-units-mod-p-proof`; lane proof by bh-free-26,
elementary, not independently reviewed). No priority is claimed.

## Statement

Let `p` be a prime, `L_p = L_(F_p)(1,2)`, `R = L_p ⊗ L_p`, and `P_p = R^x / F_p^x`. Write
`∀·Mod_pP` for the class of languages

`{w : for every x, #{y : Q(w,x,y)} ≡ 0 (mod p)}`

with `Q` polynomial-time and `|x|, |y|` polynomial in `|w|`. For prime `p` it equals
`coNP^(Mod_pP)`, because `Mod_pP` is closed under complement and under polynomially many
conjunctions (Beigel--Gill, TCS 103, 1992).

1. **The host.** `P_p` is finitely presented and simple. Here `K_1(R) = K_2(R) = 0`
   (`prime-field-leavitt-tensor-powers-have-trivial-k-theory`, the case `d = 2`), and `L_p` is
   central simple and finitely presented. So parts 3--4 of
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` make `R^x` finitely presented
   and `R^x / F_p^x` simple. Dividing by the finite centre keeps finite presentation. This
   inherits that node's conditions (the imported criteria of Khanh).
2. **Hardness (unconditional).** For an explicit finite set `Λ_p ⊂ R^x`, a polynomial-time
   map sends a circuit `Q(x,y)` of size `s` to a word `W_Q` over `Λ_p`, of length `O(s^3)`,
   such that

   `W_Q ∈ F_p^x  ⇔  W_Q = 1  ⇔  for every x, #{y : Q(x,y) = 1} ≡ 0 (mod p).`

3. **Upper bound (unconditional).** Every finitely generated subgroup of `R^x`, and of
   `R^x / F_p^x`, has word problem in `∀·Mod_pP`.
4. **Conclusion.** `WP(P_p)` is `∀·Mod_pP`-complete under polynomial-time many-one reductions,
   for every finite generating set. For `p = 2`, `P_2 = R^x` is the group of
   `leavitt-square-units-have-conp-parity-p-complete-word-problem`.

## Consequences

- **Outside the polynomial hierarchy, conditionally.** By Toda--Ogiwara (SIAM J. Comput. 21,
  1992), `PH ⊆ BPP^(Mod_pP)`. If `WP(P_p) ∈ Σ_j^p`, then `Mod_pP ⊆ Σ_j^p`. With
  Sipser--Gács--Lautemann relativized, `PH ⊆ BPP^(Σ_j^p) ⊆ Σ_(j+2)^p`, so the polynomial
  hierarchy collapses. So unless PH collapses, no `P_p` has word problem in PH. Every
  Thompson-like finitely presented simple group whose complexity is known has word problem in
  `coNP` (`fp-simple-groups-with-arbitrarily-complex-word-problem`, items 3 and 6).
- **Infinitely many complexity types.** For distinct primes `p, q`, an embedding `P_p ↪ P_q`
  would give `Mod_pP ⊆ ∀·Mod_qP`. Relative to oracles this inclusion fails, via
  Razborov--Smolensky lower bounds for `MOD_p` in `AC^0[q]` circuits. So complexity theory
  predicts that the `P_p` are pairwise non-embeddable. No group-theoretic proof of this is
  known here.

## Scope

- Nothing in the hardness proof uses the characteristic. In place of the characteristic-two
  formula of `leavitt-square-units-wp-complexity-proof` §2, the superposition letter
  `τ = s_0 + s_1` is realized by the transvection `1 + a_1 a_0^*` (`(1 + a_1 a_0^*) a_0 = τ`).
- More tensor factors or other Leavitt algebras over `F_p` give nothing harder
  (`leavitt-tensor-unit-word-problems-have-one-counting-quantifier`).
