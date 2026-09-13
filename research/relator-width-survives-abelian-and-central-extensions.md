---
rg: 2
id: relator-width-survives-abelian-and-central-extensions
kind: claim
title: Bounded relator width over a class of finite groups survives central and abelian extensions, so it holds over abelian-by-nilpotent groups
distinct_from:
  relator-width-over-nilpotent-by-locally-finite-groups: that puts a nilpotent group under a quotient from a fixed locally finite variety; this puts an abelian group under a quotient from any class with bounded width, for example nilpotent groups of unbounded class.
  simple-nonsofic-width-over-bounded-composition-factor-groups: that is the open claim over all groups with bounded composition factors; this settles its first concrete case, abelian-by-nilpotent groups, including coprime `A ⋊ B`.
---

**ESTABLISHED** by `relator-width-survives-abelian-and-central-extensions-proof`.

Let `G = <X | R>` be a finitely presented group with no nontrivial finite quotient. For a finite group `Q`
and `a in Q^X`, `w_Q(a)` is the least `k` such that every `a_x` is a product of at most `k` `Q`-conjugates of
elements `r(a)^(+-1)`, `r in R`. For a class `𝒞` of finite groups put `K(𝒞) = sup { w_Q(a) : Q in 𝒞, a in Q^X }`.

Fix once, in `F = F(X)`, an identity `x = c_x · rho_x` for each `x in X`, where `c_x = prod_i [u_i, v_i]` is a
product of commutators and `rho_x` is a product of at most `L_0` conjugates of relators. It exists because `G`
is perfect. Put `L = max_x sum_i |v_i|`.

- **(a) Central extensions.** If `Q` has a central subgroup `Z` with `Q/Z in 𝒞`, then
  `w_Q(a) <= 2 L K(𝒞) + L_0`.
- **(b) Abelian extensions.** Let `A` be an abelian normal subgroup of `Q` and suppose that every tuple of `Q/A`
  and of `Q/[A, Q]` has width at most `K` and `K'` respectively. Then `w_Q(a) <= K' + 2 |X| K`.
  Since `Q/[A, Q]` is a central extension of `Q/A`, (a) gives `K' <= 2 L K + L_0` when `Q/A in 𝒞`.
- **(c) Abelian-by-nilpotent groups.** If `A` is abelian and `Q/A` is nilpotent, of any class, then
  `w_Q(a) <= K_nil + 2 |R|`, where `K_nil = max_x K(x)` is the template constant of
  `perfect-group-relator-width-over-nilpotent-groups`.

**Consequences.**
- Bounded width over `𝒞` gives bounded width over every class `(abelian)^l`-by-`𝒞` with `l` fixed.
- By (c), the coprime case `A ⋊ B` with `B` nilpotent, named as the first concrete case in
  `simple-nonsofic-width-over-bounded-composition-factor-groups`, has bounded width. No coprimality, no bound
  on primes and no bound on the class of `B` is needed. These groups have unbounded derived length and
  unbounded Fitting quotient.
- `G` needs neither simplicity nor nonsoficity here.

**The key identity.** If a finite group acts on a finite abelian group `A` and the elements `s_1, ..., s_n`
generate the acting group, then `[A, Q] = [A, s_1] ··· [A, s_n]`, and each `[gamma, s]` is a product of two
conjugates of `s^(+-1)`. Pontryagin duality gives the identity: both sides have the same annihilator, the
characters fixed by the action.

**Where this stops.** An abelian layer costs an additive `2|X|K`, but a central layer multiplies the constant
by `2L`. Iterating (a) and (b) therefore bounds the width only for boundedly many layers above `𝒞`.
Nilpotent-by-nilpotent groups whose kernel has unbounded class are not covered.
