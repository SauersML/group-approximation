---
rg: 2
id: coprime-uhf-stabilizations-detect-uct
kind: claim
title: A nuclear algebra satisfies the UCT iff it does after absorbing each of two coprime UHF algebras
distinct_from:
  kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras: that reduces Problem II to one class of algebras; this is a permanence theorem for an individual algebra that splits its UCT into two UHF-localized halves.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (derivation, this repository).**  Let `A` be separable and nuclear,
and let `s`, `t` be coprime supernatural numbers, neither equal to `1`.  Then

```text
A satisfies the UCT   iff   A ⊗ M_s and A ⊗ M_t satisfy the UCT.     (CU1)
```

**The UCT-support filter.**  For a set `P` of primes write `M_{P^∞}` for the UHF
algebra of supernatural type `∏_{p ∈ P} p^∞`, with `M_{∅^∞} = C`, and put

```text
𝒫(A) = { P : A ⊗ M_{P^∞} satisfies the UCT }.
```

Then `𝒫(A)` is upward closed and closed under finite intersections.  Moreover `A`
satisfies the UCT iff `∅ ∈ 𝒫(A)` iff `𝒫(A)` contains two disjoint sets, and
`𝒫(A)` is nonempty iff `A ⊗ Q` satisfies the UCT (`Q` the universal UHF algebra).
So the UCT-support of a non-UCT algebra is a proper filter on the primes, or
empty.  In particular, for a non-UCT `A`, at most one prime `p` makes
`A ⊗ M_{p^∞}` satisfy the UCT.

Proof: `coprime-uhf-stabilizations-detect-uct-proof`.

**Credit.**  The literature read for this lane (Dadarlat 2003;
Brown--Browne--Willett--Wu 2020; Willett--Yu; Jaime--Willett; the STW problem
list) does not state (CU1) or the filter.  The argument is the dimension-drop
trick and may well be folklore; it is recorded here with a complete proof and
no priority claim.
