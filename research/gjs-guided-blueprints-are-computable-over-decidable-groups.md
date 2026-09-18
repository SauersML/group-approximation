---
rg: 2
id: gjs-guided-blueprints-are-computable-over-decidable-groups
kind: claim
title: Over an infinite finitely generated group with solvable word problem, the Gao--Jackson--Seward greedy blueprint is computable, its sets Delta_k are uniformly decidable, and copying along Delta_n gives an explicit recurrence set F_n F_n^-1
distinct_from:
  gjs-countable-groups-have-free-minimal-subflows: that imports the non-effective existence of free minimal subflows; this proves only that the first layer of the GJS machinery (growth sequence, guided centered blueprint, Delta_k membership, recurrence sets) is computable, and says nothing about the colouring built on top.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), an effectively closed minimal free subshift; this is one ingredient of an effective GJS attempt at (M2), and by itself yields no subshift.
  rf-toeplitz-subshift-has-computable-language: that is a Toeplitz construction over effectively residually finite groups with finite-index subgroup hierarchies; this uses GJS blueprints, whose Delta_n are not subgroups and exist over every infinite group with solvable word problem.
---

**ESTABLISHED** (route `gjs-guided-blueprints-are-computable-over-decidable-groups-proof`).

**Setting.** `G` is an infinite group with a finite generating set and solvable
word problem. Elements are handled as shortlex normal forms, so balls `B(R)` are
computable finite lists, and products and equality are decidable. GJS below is
S. Gao, S. Jackson, B. Seward, *Group colorings and Bernoulli subflows*,
arXiv:1201.0513 (Memoirs AMS 241, 2016), with the left action
`(g·x)(h) = x(g^-1 h)` on `k^G`.

**Statement.** There are a growth sequence `(H_n)` (GJS Definition 5.3.2) and a
centered, directed, maximally disjoint blueprint `(Delta_n, F_n)` guided by it
(GJS Definition 5.3.4) such that:

1. **Computable layers.** `n ↦ H_n`, `n ↦ F_n` and `(n,k) ↦ D^n_k` (for `k <= n`)
   are computable maps to finite lists.
2. **Decidable Delta.** For `n >= k` and `g ∈ H_n`,
   `g ∈ Delta_k  <=>  g ∈ D^{n+2}_k`.
   So `{(g,k) : g ∈ Delta_k}` is decidable.
3. **Explicit recurrence set.** Let `x ∈ k^G`, let `A ⊆ G` be finite and let `n`
   satisfy `x(γa) = x(a)` for all `γ ∈ Delta_n` and `a ∈ A`. Then
   `∀g ∈ G ∃t ∈ F_n F_n^-1 ∀a ∈ A : x(gta) = x(a)`.
   In particular, if a computable `x` has a computable level function `A ↦ n(A)`
   with this copying property, then `x` is a minimal point (GJS Lemma 2.4.5)
   and the recurrence set `T(A) = F_{n(A)} F_{n(A)}^-1` is computable.

**What this does not give.** Item 3 bounds the return times of patterns
centred at the identity. It does not bound where an arbitrary pattern of `x`
first occurs. (M2) needs that stronger bound, which is equivalent to a decidable
language. See Attempt 2 of `decidable-fp-groups-have-effective-minimal-free-subshifts`.
