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

**Credit (corrected 2026-09-12).**  The forward direction of (CU1) for UHF types
`p^∞` and `q^∞` with `p`, `q` relatively prime is Barlak--Szabó, *Rokhlin actions
of finite groups on UHF-absorbing C\*-algebras*, Trans. Amer. Math. Soc. 369
(2017), arXiv:1403.7312, Proposition 4.16, proved with the same dimension-drop
algebra and the Jiang--Su algebra as its stationary limit.  The earlier note that
no source read states (CU1) is withdrawn.  The filter reformulation is recorded
here without priority claim.  Their Theorem 4.17 characterizes Problem II through
`Z_p`- and `Z_q`-crossed products of `O_2` for any two primes, and Barlak--Li II
Corollary 4.17 cites Proposition 4.16 for the pair `2, 3`
(`barlak-li-uct-iff-z2-z3-actions-fix-cartan`).  Sources:
`research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md`.
