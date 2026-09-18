---
rg: 2
id: bruhat-tits-skew-field-sl-tits-system-bornology
kind: claim
title: For SL_m over a skew field with a discrete valuation, Bruhat-Tits give an affine Tits system whose double-coset bornology is entrywise boundedness below
distinct_from:
  gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings: that is about GL_n(Q) on p-adic buildings over commutative local fields; this imports the Bruhat-Tits statements for an arbitrary skew field, possibly of infinite rank over its centre, with a discrete valuation, and the identification of their Tits-system bornology with the entrywise one.
---

**ESTABLISHED (import).**

**Statement.** Let `K` be a skew field (not necessarily commutative, of any
rank over its centre) with a nontrivial discrete valuation `ω`, let
`X = K^m` (right vector space, `m ≥ 2`) and `G = SL(X) = SL_m(K)`, the
kernel of the Dieudonné determinant. Then:

1. There are subgroups `B, N ≤ G` and a finite set `S` such that
   `(G, B, N, S)` is a Tits system whose Weyl group `W = N/(B ∩ N)` is an
   affine Coxeter group (type `Ã_{m-1}`), `S` finite.
2. The Tits axioms hold in Bourbaki's form: `w ↦ BwB` is a bijection
   `W → B\G/B`; `sBw ⊂ BwB ∪ BswB` for `s ∈ S`; and
   `BsB·BwB = BswB` if and only if `ℓ(sw) = ℓ(w) + 1`.
3. The set of parts of `G` with finite image in `B\G/B` is a bornology
   compatible with the group law. It coincides with the set of parts `M`
   such that `{ω(g_ij) : g ∈ M, 1 ≤ i, j ≤ m}` is bounded below.

**Source.** F. Bruhat and J. Tits, *Groupes réductifs sur un corps local. I*,
Publ. Math. IHÉS 41 (1972), 5–251, numdam PMIHES_1972__41__5_0: (1.2.6)–(1.2.8),
(3.1.3)–(3.1.4), 6.5, (8.1.7), (10.2.1)–(10.2.7).

**Citation route:** `bruhat-tits-skew-field-sl-tits-system-bornology-citation`.
