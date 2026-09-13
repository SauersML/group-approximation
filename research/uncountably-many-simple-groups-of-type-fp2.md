---
rg: 2
id: uncountably-many-simple-groups-of-type-fp2
kind: claim
title: "There are uncountably many pairwise non-isomorphic simple groups of type FP_2"
---

There is a family of simple groups of type FP_2 (over `Z`) containing
uncountably many isomorphism types.

This is the affirmative answer to the first part of Zaremsky's Problem 1.20
(`zaremsky-1-20-uncountably-many-simple-fp2-groups`).

## Attempts

- **Reformulation (established, 2026-09-13).** By
  `simple-fp2-uncountability-via-perfect-simple-quotients`, this claim holds if
  and only if some finitely presented group `H` has uncountably many perfect
  normal subgroups `N` with `H/N` simple. The work is therefore to find one
  such `H`.
- **Dead: finite-data self-similar constructions.** The Llosa
  Isenrich–Schesler–Wu machine (commutator subgroups of Röver–Nekrashevych
  groups `V_d(G)` of finitely generated self-similar groups `G`) cannot give
  uncountably many groups. Every finitely generated subgroup of such a
  `V_d(G)` has co-r.e. word problem
  (`rover-nekrashevych-groups-have-co-re-word-problem`), and only countably
  many finitely generated groups have r.e. or co-r.e. word problem
  (`fg-groups-with-re-or-co-re-word-problem-are-countable`). In any witnessing
  family, all but countably many members have word problem that is neither
  r.e. nor co-r.e.
- **Dead: a simple ambient group.** A simple `H` has no proper nontrivial
  quotients.
- **Dead: free products of simple groups.** In `H = A * B` with `A`, `B`
  simple, a normal subgroup `N` meeting both factors trivially is free by the
  Kurosh subgroup theorem, so it is not perfect unless trivial. If `N` meets a
  factor nontrivially it contains that factor, and the quotient is a quotient
  of the other factor.
- **Open candidate: restriction to invariant sets.** Take `H` finitely
  presented and acting on a Cantor space `X` through the germs of an ample
  groupoid `G` that has uncountably many minimal closed invariant subsets `Y`.
  Suppose restriction `H -> A(G|_Y)` is onto the alternating group of the
  restricted groupoid with perfect kernel, and `A(G|_Y)` is simple
  (Nekrashevych, for minimal effective groupoids). Then the quotients are
  simple of type FP_2, and distinct `Y` give distinct kernels, hence
  uncountably many isomorphism types. Candidate: `G = G_V × (Z ⋉ {0,1}^Z)`
  (the Cuntz groupoid of `V` times the full two-sided shift), with `Y = C ×`
  (a Sturmian subshift). Open: finite presentability of `A(G)`, surjectivity
  of the restriction, and perfectness of its kernel.
- **Open candidate: uniform relators over Leary's parameter.** Find a finite
  relator set `R'` such that `⟨X | R_0 ∪ R' ∪ {long cycle relators for n ∈ S}⟩`
  is simple for uncountably many `S`, in the style of Leary's presentations
  `P_L(Γ, S)`. Adding relators that normally generate perfect subgroups keeps
  type FP_2, but no candidate `R'` is known.
