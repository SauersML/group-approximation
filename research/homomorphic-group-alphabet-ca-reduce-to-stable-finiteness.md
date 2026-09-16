---
rg: 2
id: homomorphic-group-alphabet-ca-reduce-to-stable-finiteness
kind: claim
title: Injective homomorphic automata over any finite group alphabet are surjective once the group algebras at its abelian composition primes are stably finite
distinct_from:
  homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness: that covers solvable alphabets only, cites the linear base case, and leaves nonabelian composition factors open; this covers every finite group alphabet, imposes hypotheses only at primes of abelian composition factors with p^n <= |K|, is unconditional when there is no abelian composition factor, and proves the linear base case in full
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided pair over k[G] into a strict linear automaton; this is the converse direction for automata that are group homomorphisms over arbitrary finite group alphabets, and the resulting equivalence weakly surjunctive = linearly surjunctive
artifacts:
  - research/artifacts/homomorphic-group-alphabet-surjunctivity-2026-09-16.md
---

Let `G` be any group and `K` any finite group. A cellular automaton `K^G -> K^G` is **homomorphic** if it is a
group homomorphism for pointwise multiplication. Let `P(K)` be the set of primes `p` such that `Z/p` is a
composition factor of `K`.

1. **Reduction.** Suppose `M_n(F_p[G])` is directly finite for every `p` in `P(K)` and every `n >= 1` with
   `p^n <= |K|`. Then every injective homomorphic automaton `K^G -> K^G` is surjective.
   - For every `G`, `p` and `n`: every injective `F_p`-linear automaton on `(F_p^n)^G` is surjective if and only
     if `M_n(F_p[G])` is directly finite. So the hypothesis may equally be read as linear surjunctivity at those
     `(p, n)`.
   - Contrapositively, a strict homomorphic automaton over `K` gives a strict `F_p`-linear automaton of rank `n`,
     with `p` in `P(K)` and `p^n <= |K|`.
2. **Unconditional case.** If `K` has no abelian composition factor, then for every group `G` every injective
   homomorphic automaton on `K^G` is bijective. Examples are finite products of nonabelian simple groups and
   iterated permutational wreath products of them.
3. **Equivalence.** For every group `G` the following are equivalent.
   - Every injective homomorphic automaton over every finite group alphabet is surjective. This is "weakly
     surjunctive", Phung, arXiv:2111.13607v2, Definition 1.2.
   - Every injective linear automaton over every finite-dimensional vector space over a finite field is
     surjective. This is "linearly surjunctive", same paper, Definition 6.1.
   - `F_p[G]` is stably finite for every prime `p`.

**What is new.**
- `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness` handles solvable `K` through the derived series.
  Its Scope leaves all finite `K` open.
  - Here the filtration is the socle instead.
  - Invariance of the socle is forced by first proving that the local rule is surjective.
  - The nonabelian socle layer of an injective automaton is shown to be a permuted shift, for every `G`.
- Phung (2021) records only the inclusion weakly surjunctive ⊆ linearly surjunctive, and asks in Question 1
  whether a non weakly surjunctive group exists. Part 3 gives the reverse inclusion.

**Remark (not part of this claim).** Part 3 together with the ESTABLISHED `stable-finiteness-reduces-to-prime-field`
says that `G` is weakly surjunctive exactly when `k[G]` is stably finite for every field `k`. So Phung's Question 1
is exactly the question whether Kaplansky's stable finiteness conjecture fails for some group.

**Scope.**
- This establishes surjunctivity of no new group. It shows that the homomorphic sub-problem of Gottschalk's
  conjecture has no content beyond the linear one.
- Nonlinear local rules, and rules that are homomorphic only on a sub-alphabet, are not covered.
