---
rg: 2
id: fp-alt-fin-envelopes-are-unique-solutions-of-their-relators
kind: claim
title: A finitely presented permutation group generated over a fixed Alt_fin-containing group is the only solution of its relators
distinct_from:
  shift-envelope-fp-enumerations-are-countable: that counts the enumerations of one input that give finitely presented envelopes; this says a finite presentation singles out the extra generating permutations among all tuples in Sym(Omega)^k, for any generators and no input group.
  cyclic-shift-finite-prefix-cannot-decide-fp: that shows finite point samples cannot certify finite presentation of an envelope; this shows that a finite presentation, once it exists, determines the generating permutations completely.
---

**ESTABLISHED** by `fp-alt-fin-envelope-relator-uniqueness-proof`.

Let `Omega` be an infinite set and `S_0 ⊂ Sym(Omega)` a finite set with
`<S_0> ⊇ Alt_fin(Omega)`. Let `gamma = (gamma_1, ..., gamma_k) ∈ Sym(Omega)^k`
and `G = < S_0, gamma_1, ..., gamma_k > <= Sym(Omega)`.

1. **Uniqueness.** Suppose `G` is finitely presented, and let `R` be a finite
   set of words in the letters `S_0 ⊔ {g_1, ..., g_k}` and their inverses that
   presents `G` under `s -> s`, `g_i -> gamma_i`. Then `gamma` is the only tuple
   `gamma' ∈ Sym(Omega)^k` such that every `r ∈ R` evaluates to the identity
   permutation of `Omega` when each `s ∈ S_0` is read as `s` and each `g_i` as
   `gamma'_i`.
2. **Computability.** Take `Omega = N`. Suppose every `s ∈ S_0` and its
   inverse are computable, and some recursive `D : N -> N` satisfies
   `gamma_i(x) <= D(x)` and `gamma_i^-1(x) <= D(x)` for all `i` and `x`. If `G`
   is finitely presented, each `gamma_i` is computable.

Clause 1 needs no support, displacement or decidability hypothesis. Its
mechanism, that a homomorphism fixing `Alt_fin(Omega)` pointwise fixes every
permutation it is defined on, is the centralizer argument already used in
`shift-envelope-countability-rigidity-proof`. No novelty is claimed.

Clause 2 bounds nothing: a unique solution can be arbitrarily hard to compute.
Its use is to reduce questions about finite presentation to questions about
unique solutions of finite relator systems, as in
`fp-bounded-displacement-e2-envelopes-are-eventually-periodic`.
