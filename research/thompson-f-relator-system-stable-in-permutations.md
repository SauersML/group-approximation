---
rg: 2
id: thompson-f-relator-system-stable-in-permutations
kind: claim
title: The two relators of Thompson's F are stable in permutations (Arzhantseva--Paunescu Open problem)
root: true
distinct_from:
  almost-commuting-permutations-are-near-commuting: that is the proved stability of the commutator system; this is the Thompson two-relator system, whose stability is open.
  thompson-f-is-not-sofic: that is the group-level statement; this is the finitary permutation statement Arzhantseva and Paunescu posed, equivalent to it by thompson-f-sofic-iff-relator-system-unstable.
---

**OPEN.** The system `R = {[ab^-1, a^-1ba], [ab^-1, a^-2ba^2]}` is stable in permutations with the
normalized Hamming distance (Arzhantseva--Păunescu, arXiv:1410.2626v2, Definition 3.2). Equivalently, by
`almost-commuting-permutations-are-near-commuting`, every `delta`-solution `(A, B)` in `Sym(n)` has
`d(AB, BA) < epsilon(delta)` with `epsilon(delta) -> 0` uniformly in `n`.

*Marked root: a named open problem.* Arzhantseva--Păunescu, p. 3, verbatim: "Open problem. Is the system
of two words [ab^-1, a^-1ba] and [ab^-1, a^-2ba^2] (weakly) stable in permutations?" Their "weakly"
variant (their Definition 7.1, not read) is not recorded here.

**Equivalence.** By `thompson-f-sofic-iff-relator-system-unstable` this claim holds exactly when `F` is
not sofic. It then makes `V` nonsofic too.

## Attempts

- **Exact solutions.** They all commute, since finite quotients of `F` are abelian. This is the
  finite-group shadow of the claim, and it does not reach `delta`-solutions.
- **Kazhdan compression.** No instance: `F` has the Haagerup property
  (`a-t-menable-groups-have-no-rigid-compression-defect`).
- **Uniform stability.** Fournier-Facio--Rangarajan, arXiv:2301.03970, prove uniform stability of `F`
  for submultiplicative norms. Their text says the pointwise permutation statement "would imply that F
  is not sofic", and they treat it as out of their scope.
