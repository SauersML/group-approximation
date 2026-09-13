---
rg: 2
id: b-tilde-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every Euclidean Artin group of type B̃_n embeds in Aut(F_M), satisfies permutational Boone--Higman, and embeds in a finitely presented simple group
distinct_from:
  c-tilde-artin-groups-satisfy-permutational-boone-higman: that settles type C̃_n through a braid group embedding; this settles type B̃_n, where Allcock gives only orbifold braid pictures, through the free fibre group of the Li--Roushon fibration.
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A and the Artin types of its Corollary B (A, B = C, D, I_2(m), Ã); this adds the Euclidean type B̃_n, which BFFHZ list as open.
  b-tilde-artin-complement-fibres-over-configuration-space: that is the topological input, a fibration of an arrangement complement imported from Li--Roushon; this is the group-theoretic consequence, which the source does not draw.
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups; this settles the single Euclidean family B̃_n.
artifacts:
  - research/artifacts/bh-b-tilde-artin-2026-09-12.md
---

**ESTABLISHED.** For every `n >= 3`, the Artin group `A(B̃_n)`:
- embeds in `Aut(F_M)`, where `M = 2^n · n! · (3n·2^(n−1) + n + 2)` (for
  `n = 3`, `M = 1968`);
- lies in the permutational Boone--Higman class, i.e. embeds in a group with an
  action of type (A);
- embeds in a finitely presented simple group, a twisted Brin--Thompson group.

**Why it matters.** It closes a case of Problem 5.3(13) in arXiv:2306.16356v3
that the two most recent sources list as open.
- **Survey Remark 5.4**, p. 18, read from the PDF on 2026-09-12: item (13)
  "remains open for many classes of Artin groups, including those of exceptional
  spherical type and those of Euclidean type other than the Ã_n and triangle
  cases (C̃_2 and G̃_2)".
- **BFFHZ**, arXiv:2503.21882v2, after Corollary B, as quoted in
  `c-tilde-artin-groups-satisfy-permutational-boone-higman` (not re-read in
  this lane): Boone--Higman "remains open for the exceptional type spherical
  Artin groups, and the Euclidean Artin groups other than type ~An; in rank 3
  it is also known for type ~C2 and ~G2".
- `artin-groups-satisfy-boone-higman`, Attempts 1, records that the braid-group
  route dies for B̃_n.

**Credit and scope.**
- **The ingredients are known.**
  - The fibration and the chain of spaces are Li--Roushon's
    (`b-tilde-artin-complement-fibres-over-configuration-space`). They use them
    to prove virtual poly-freeness.
  - The permutational property of `Aut(F_m)` is BFFHZ's, and the simple envelope
    for subgroups is Zaremsky's.
  - The remaining steps are classical: the centreless-kernel embedding, Artin's
    representation, and Krasner--Kaloujnine.
- **What this adds** is the combination. The fibre group of the Li--Roushon
  fibration is free of rank at least 37, hence centreless. So a finite-index
  subgroup of `A(B̃_n)` lands in `Aut(F_r) × P_(n+1) <= Aut(F_(r+n+1))`.
- **The novelty search was bounded**, on 2026-09-12:
  - an arXiv abstract search for "Boone-Higman", through arXiv:2609.01868;
  - the newest 20 arXiv results for "affine Artin", through arXiv:2509.00445;
  - four web searches combining B̃_n with Aut(F_n), residual finiteness and
    Boone--Higman.

  None of them settles B̃_n. No priority is claimed for any ingredient.
- **Residual finiteness.** `A(B̃_n)` is residually finite, because `Aut(F_M)` is
  (Baumslag). The novelty of this corollary was not searched separately.
- **Types not covered.**
  - D̃_n: its arrangement has no hyperplanes `u_k ∈ Z`, so the Möbius step of the
    chain fails. No fibration with free fibres is known for it.
  - F̃_4, Ẽ_6, Ẽ_7 and Ẽ_8 are not addressed.

The derivation is `b-tilde-artin-pbh-via-free-fibre-kernel-proof`.
