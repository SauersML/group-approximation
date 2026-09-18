---
rg: 2
id: almost-everywhere-hard-recursive-sets-exist
kind: claim
title: For every total recursive time bound there is a recursive set that every decision procedure decides slowly on all but finitely many inputs
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups whose word problems beat a time bound; this is the classical recursion-theoretic fact (Rabin 1960) that recursive sets exist which are hard on almost every input, with no group in sight.
  complexity-bounded-host-classes-are-not-universal: that uses an infinitely-often diagonalization to show bounded host classes are not universal; this is the almost-everywhere form of the diagonalization, which is what lets a hardness bound hold at every scale rather than on a sparse set.
---

**ESTABLISHED.** Let `F: N -> N` be total recursive. There is a recursive set
`A ⊆ N` such that for every deterministic Turing machine `M` that decides `A`
(input `i` written in binary, output `1` iff `i ∈ A`), the running time of `M`
on input `i` exceeds `F(i)` for all but finitely many `i`.

This is M. O. Rabin, *Degree of difficulty of computing a function and a
partial ordering of recursive sets*, Tech. Rep. 2, Hebrew University, 1960 (not
re-read). The proof route below is self-contained and uses only a standard
enumeration `M_0, M_1, ...` of Turing machines and step-counted simulation.

**Model test.** Read "infinitely often" instead of "almost everywhere" and the
statement is the ordinary time hierarchy. The almost-everywhere form is stronger:
a set that is easy on a sparse infinite set of inputs (say all powers of two)
is excluded. The construction handles this by cancelling a machine at the first
stage where it is fast, so a machine that decides `A` can be fast on only
finitely many inputs.

DERIVATION
almost-everywhere-hard-recursive-sets-exist-proof
