---
rg: 2
id: ln-completion-word-problem-reduces-to-base-algebra
kind: claim
title: The word problem of a Leavitt--Nekrashevych completion reduces to that of its base with a fixed elementary blow-up, so completions over free bases are not universal hosts
distinct_from:
  leavitt-nekrashevych-completion-embeds-and-is-fp: that proves finite presentation of O_psi and injectivity of B -> O_psi; this bounds the cost of the word problem of O_psi by the cost of the word problem of B.
  no-fp-simple-algebra-hosts-every-decidable-algebra: that is the complexity principle for any host class with one shared recursive time bound; this shows that Leavitt--Nekrashevych completions over a base class with a shared bound, in particular over free algebras, form such a host class.
  decidable-algebras-embed-in-simple-ln-completions: that is the open premise asking for simple completions hosting every decidable algebra; this shows the complexity such hosts need cannot come from the recursion psi and must sit in the relators of B.
---

**ESTABLISHED** through `ln-completion-word-problem-reduction-proof`.

Notation as in `leavitt-nekrashevych-completion-embeds-and-is-fp`. Let `K` be a
computable field, `B = K<g_1..g_m | R>` a finitely generated unital algebra, and
`psi : B -> M_d(B)` an **injective** matrix recursion, `d >= 2`. Fix noncommutative
polynomials `p_{k,ij}` in the `g`'s with `psi(g_k)_{ij} = p_{k,ij}` in `B`. Let
`D >= 1` bound their degrees and `c >= 1` bound their numbers of monomials. The
**length** of an expression is its number of letters, as in step 3 of
`no-fp-simple-algebra-hosts-every-decidable-algebra-proof`: an expression is a
product of noncommutative polynomials in `g_k, s_i, t_i`.

**Claim.**

1. **Reduction.** Let `w` be an expression of length `l`, and `w_k` the part of
   its expansion of degree `k` (`deg s_i = 1`, `deg t_i = -1`, `deg g = 0`). Then
   `w = 0` in `O_psi` iff for every `k` with `|k| <= l` and all words `mu, nu` over
   `{1..d}` with `|mu| = l + k`, `|nu| = l`, the noncommutative polynomial
   `Y_{mu nu}(w_k)` in the `g`'s, computed by the explicit procedure of the
   route, is zero in `B`. Each `Y_{mu nu}(w_k)` has degree at most `l D^{3l}` and
   at most `(dc)^{8 l^2 D^{3l}}` monomials.
2. **Uniform bound.** There is a recursive nondecreasing `T_K : N -> N`, depending
   only on `K`, with the following property. If the zero test for noncommutative
   polynomials in `B` takes time `F_B(n)` on inputs of size `n`, then the word
   problem of `O_psi` on expressions of length `l` is solved in time
   `T_K(C l) + T_K(C l) F_B(T_K(C l))`, where `C` depends only on `d, m, D, c` and
   the codes of the coefficients of the `p_{k,ij}`.
3. **Free bases give no universal host.** Let `H_free` be the class of all
   completions `O_psi` over free algebras `B = K<g_1..g_m>`, for all `m, d` and all
   injective recursions `psi`. Then `H_free` satisfies the hypothesis of
   `no-fp-simple-algebra-hosts-every-decidable-algebra` for one recursive `T`. So
   there is a decidable `X ⊆ N` whose monomial algebra
   `A_X = K<x,y>/(x y^n x : n in X)` embeds in no member of `H_free`. The same holds
   for completions over any base class whose polynomial zero tests share one
   recursive bound, such as commutative polynomial rings.
4. **Consequence for the premise.** In `decidable-algebras-embed-in-simple-ln-completions`,
   the recursion `psi` adds at most a fixed elementary overhead to the word problem
   of `B`. So for the benchmark inputs `A_X`, the decision procedure for `X` must
   be carried by the relators of the finitely presented base `B`, not by `psi`.
   Transducer recursions over free bases (Attempt 3 there) cannot host every `A_X`,
   whatever their minimality and aperiodicity.

No novelty is claimed. Parts 1 and 2 are a bookkeeping form of the normal form in
`leavitt-nekrashevych-completion-simplicity-criterion`, and part 3 is the
complexity principle applied to that bound.

## Scope note (2026-09-18, lane `bh-algebra`)

Part 3's class `H_free` consists of completions along *injective* recursions. A non-injective
recursion `ψ` on a free algebra `B` gives a finitely presented `O_ψ(B)` whose base is the self-similar
quotient `B/J` (`noninjective-ln-completions-have-self-similar-bases`). Parts 1 and 2 then
reduce its word problem to membership in `J`, which this node does not bound. So parts 3 and 4 do not
cover transducer recursions whose iterates have nontrivial kernel.
