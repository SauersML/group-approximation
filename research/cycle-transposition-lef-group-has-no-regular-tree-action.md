---
rg: 2
id: cycle-transposition-lef-group-has-no-regular-tree-action
kind: claim
title: A two-generated residually finite group with polynomial-time word problem acts faithfully on no regular rooted tree
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that excludes inputs that are not residually finite, such as Thompson's V, from self-similar hosts; this gives a residually finite input with polynomial-time word problem that lies in no self-similar group, and indeed acts faithfully on no regular rooted tree.
  regular-tree-torsion-orders-have-primes-at-most-degree: that is the general torsion bound for automorphisms of T_d; this is an explicit residually finite group, with elements of every prime order at least 5, to which the bound applies.
artifacts:
  - research/artifacts/regular-tree-torsion-obstruction-2026-09-12.md
---

**ESTABLISHED.** For `n >= 3`, let `sigma_n` be the rotation `x -> x+1` of
`Z/n` and let `tau_n` be the transposition `(0 1)`. Put

```text
Gamma = < sigma, tau >  <=  prod_(n >= 3) Sym(Z/n),     sigma = (sigma_n)_n,  tau = (tau_n)_n.
```

Then:

1. `Gamma` is residually finite.
2. The word problem of `Gamma` is decidable in polynomial time.
3. For every prime `p >= 5`, `Gamma` contains a subgroup isomorphic to `Alt(p)`
   whose elements are trivial in every coordinate except `n = p`. So `Gamma`
   has elements of order `p` for every prime `p >= 5`.
4. `Gamma` embeds in `Aut(T_d)` for no `d`, so it is a subgroup of no
   self-similar group.
5. `Gamma` is residually `W_d` for no `d`, in the notation of condition (N1) of
   `every-fp-rf-group-embeds-in-fp-self-similar-group`. Every quotient of
   `Gamma` lying in `W_d` kills the copies of `Alt(p)` with `p > d`.

**What this shows.**
- Condition (N1) is a genuine obstruction for finitely generated residually
  finite groups with solvable word problem, even polynomial-time word problem.
- The finite presentation hypothesis in
  `every-fp-rf-group-embeds-in-fp-self-similar-group` carries real weight.
  Whether `Gamma` is finitely presented is not decided here.
- A finitely presented residually finite overgroup of `Gamma` would refute that
  claim; see `fp-rf-group-with-unbounded-prime-torsion` and
  `rf-higman-embedding-for-decidable-groups`.

The group is elementary, and block-diagonal subgroups of `prod Sym(n)` are
standard. No novelty is claimed for the group itself, only for its use as an
obstruction.

DERIVATION
cycle-transposition-lef-group-proof
