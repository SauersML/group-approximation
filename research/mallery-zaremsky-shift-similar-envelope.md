---
rg: 2
id: mallery-zaremsky-shift-similar-envelope
kind: claim
title: Every finitely generated group embeds in a finitely generated strongly shift-similar permutation group
distinct_from:
  boone-higman-thompson-simple-envelope: that hypothesizes a solvable word problem and produces a computably presented SIMPLE envelope; this hypothesizes nothing and produces a finitely generated envelope that is a permutation group with a self-similarity property and is not claimed simple. The absence of any hypothesis is why this envelope cannot by itself decide anything.
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's theorem, embedding every countable group in a two-generator simple group with no effectivity; this embeds every finitely generated group in a finitely generated shift-similar permutation group, and the point of the target is its action on the naturals rather than its simplicity.
  clapham-fp-embedding-preserves-word-problem: that produces a finitely PRESENTED envelope and preserves decidability; this produces a finitely GENERATED envelope with a permutation structure and preserves nothing algorithmic -- finite presentability of this envelope is exactly the open compiler statement shift-higman-compiler.
  fp-strongly-shift-similar-admits-type-a-action: that is the payoff theorem about strongly shift-similar groups that are already finitely presented; this is the universal construction, which never produces a finitely presented group and therefore never triggers the payoff on its own.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

A subgroup `G <= Sym(N)` is **shift-similar** if `psi_j(g) in G` for every
`g in G` and every `j in N`, where

    psi_j(g) = s_{g(j)}^{-1} . g|_{N \ {j}} . s_j

and `s_j` is the shift `i |-> i` for `i < j`, `i |-> i+1` for `i >= j`.  It
is **strongly** shift-similar when each `psi_j` restricted to `G` is
surjective.

Then: for every finitely generated group `P` there is a finitely generated
strongly shift-similar `G <= Sym(N)` with `P <= G`.

**Verification status.**  Read from source 2026-08-24.  Mallery--Zaremsky,
*Houghton-like groups from "shift-similar" groups*, arXiv:2202.00822 (to
appear, J. Comb. Algebra), Theorem 3.28, verbatim: "For any finitely
generated group `Gamma`, there exists a finitely generated strongly
shift-similar group `G <= Sym(N)` such that `Gamma` embeds as a subgroup of
`G`."  The definitions of `psi_j`, shift-similar and strongly shift-similar
are quoted from Zaremsky, arXiv:2405.18354, Definition 5.2.

## Notation used in this graph

The construction picks a bijection `nu : P -> N`, realizes `P` by
permutations of half-finite support (the left regular representation
transported onto the even numbers), and adjoins `E_2`, the group of
eventually 2-periodic permutations.  This graph writes the resulting group
`E_nu(P)`; that notation is **local** and is not the source's.  What the
source does record is that the bijection is an arbitrary choice -- the
theorem asserts existence and pins no particular `nu` -- and that is exactly
the freedom `shift-higman-compiler` proposes to spend.
