---
rg: 2
id: bs-free-ascending-free-hnn-extensions-satisfy-boone-higman
kind: claim
title: Every ascending HNN extension of a finitely generated free group with no BS(1,d) subgroup is hyperbolic, lies in the permutational class and embeds in a finitely presented simple group; in particular the Sapir group F(a,b)*_(a->ab, b->ba) does
distinct_from:
  power-map-free-mapping-tori-satisfy-permutational-boone-higman: that covers the permuted power maps x_i -> x_pi(i)^(m_i), whose mapping tori contain BS(1,m) and are not hyperbolic; this covers the mapping tori with no BS(1,d) at all, and settles the test case phi(x) = xy, phi(y) = yx that node leaves open.
  relative-power-map-free-mapping-tori-satisfy-pbh: that covers a monoid of endomorphisms whose mapping tori may contain BS(1,d); this covers every endomorphism whose mapping torus contains none.
  one-relator-groups-satisfy-boone-higman: that is the open problem for all one-relator groups; this covers the one-relator groups that are ascending HNN extensions of finitely generated free groups and contain no BS(1,d).
  mutanguha-ascending-hnn-hyperbolicity-criterion: that is the imported hyperbolicity criterion; this composes it with the Boone--Higman theorem for hyperbolic groups.
---

**ESTABLISHED** (composition of imported theorems; no priority claimed).

## Statement

Let `F` be a finitely generated free group and `φ : F → F` an injective endomorphism,
with ascending HNN extension `F*_φ = ⟨F, t | t x t^{-1} = φ(x) (x ∈ F)⟩`. Suppose `F*_φ`
contains no subgroup isomorphic to `BS(1,d)` for any `d ≥ 1`. Then:
1. `F*_φ` is word-hyperbolic;
2. `F*_φ` lies in the permutational class `B_A`;
3. `F*_φ` embeds in a finitely presented simple group.

## Proof

1. Item 2 ⇒ item 1 of `mutanguha-ascending-hnn-hyperbolicity-criterion`, Theorem `main`
   (for rank at least 2; in rank 1 the hypothesis never holds).
2. `hyperbolic-groups-lie-in-the-permutational-class` (lane proof read off from BBMZ).
3. `hyperbolic-groups-satisfy-boone-higman` (BBMZ, arXiv:2309.06224), independently of item 2. `∎`

## Instances

- **The Sapir group.** `φ(a) = ab`, `φ(b) = ba` on `F(a,b)`. It is word-hyperbolic by
  Mutanguha's Example `sapir` (arXiv:1908.08214), so it satisfies Boone--Higman. This is
  the test case `φ(x) = xy`, `φ(y) = yx` that
  `power-map-free-mapping-tori-satisfy-permutational-boone-higman` records as not settled.
- **Irreducible nonsurjective endomorphisms.** By Mutanguha's Theorem `hypthm` their mapping
  tori are word-hyperbolic, so all of them are covered.
- **One-relator groups.** Every one-relator group that is an ascending HNN extension of a
  finitely generated free group (for example by Brown's criterion, a letter of exponent sum
  zero whose extreme heights in the relator occur once on one side) and contains no
  `BS(1,d)` is covered. Whether this is also a consequence of Linton's hierarchy theorems
  (Theorems 7.1, 7.2 of *One-relator hierarchies*) was not checked.

## What remains among ascending HNN extensions of free groups

Exactly the mapping tori that contain some `BS(1,d)`, `d ≥ 1`. Of these, the permuted power
maps and a larger monoid of endomorphisms are in `B_A` by
`power-map-free-mapping-tori-satisfy-permutational-boone-higman` and
`relative-power-map-free-mapping-tori-satisfy-pbh`. Free-by-cyclic ones (surjective `φ`) are
covered by `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`. Mutanguha remarks,
without proof, that when there is no `BS(1,d)` with `d ≥ 2`, `F*_φ` should be hyperbolic
relative to finitely many free-by-cyclic groups (arXiv:2005.11896v2, final section). A
relatively hyperbolic Boone--Higman theorem would then cover that case, but none is on main.
