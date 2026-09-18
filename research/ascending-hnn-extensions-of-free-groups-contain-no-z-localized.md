---
rg: 2
id: ascending-hnn-extensions-of-free-groups-contain-no-z-localized
kind: claim
title: No ascending HNN extension of a finitely generated free group contains Z[1/P] for an infinite set of primes P, in particular no Z_(l) and no Q
distinct_from:
  free-group-mapping-tori-contain-no-z-localized: that proves the exclusion only when the endomorphism is injective on rational homology, through the lower central series; this proves it for every injective endomorphism, through Stallings graphs, and settles the case left open there.
  fg-metabelian-groups-have-roots-at-finitely-many-primes: that excludes finitely generated metabelian hosts; mapping tori of free groups are a different class, finitely presented and residually finite, and in general not metabelian.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
  - research/artifacts/gq-referee-a-ascending-hnn-extensions-of-free-groups-contain-no-z-localized.md
  - research/artifacts/gq-referee-b-ascending-hnn-extensions-of-free-groups-contain-no-z-localized.md
---

**ESTABLISHED (2026-09-18)** through `ascending-hnn-free-no-z-localized-proof`. Lane proof
(gq-k2-q). *Reviewed:* PASS by `gq-referee-a`
(`research/artifacts/gq-referee-a-ascending-hnn-extensions-of-free-groups-contain-no-z-localized.md`) and by
`gq-referee-b` (`research/artifacts/gq-referee-b-ascending-hnn-extensions-of-free-groups-contain-no-z-localized.md`).
Nits applied. Inputs:
- part 1 of `free-group-mapping-tori-contain-no-z-localized` (refereed PASS by gq-referee-a and gq-referee-b);
- Stallings graphs: Kapovich–Myasnikov, arXiv:math/0202285v1, Definition 2.3, Lemma 2.9 and Proposition 3.8, read at
  the source by gq-referee-b;
- uniqueness of roots in free groups, from Nielsen–Schreier.

No novelty is claimed.

## Statement

Let `F` be free of finite rank and `φ : F -> F` injective, and let `G_φ = ⟨F, t | t^(-1) x t = φ(x)⟩`.

1. **Bounded root exponents.** Let `V_φ` be the number of vertices of the Stallings graph of the subgroup `φ(F)`.
   If `r ∈ F` is not a proper power and `φ(r) = s^f` with `s` not a proper power, then `f <= V_φ`.
2. **Root sets are finite.** For `x ∈ F ∖ {1}`, write `x = r_0^(e_0)` with `r_0` not a proper power. Then every
   prime `p` with some `φ^k(x)` a `p`-th power in `F` divides `e_0` or satisfies `p <= V_φ`.
3. **Conclusion.** `G_φ` contains no subgroup isomorphic to `Z[1/P]` with `P` an infinite set of primes. In
   particular it contains no `Z_(l)`, for any prime `l`, and no `Q`.

## Consequences

- **A closed route.** Every finitely presented group of the form `F *_φ`, which is also residually finite by
  Borisov–Sapir (context only; not used), fails as a witness for `z-localized-embeds-in-fp-rf-group`. The same holds
  for free-by-cyclic groups.
- **Calibration.** For `BS(1,m)` (`F = Z`, `φ(a) = a^m`), `V_φ = m`, and the root primes are exactly the primes
  dividing `m`.
- **Generalization.** The argument uses three properties of `F`:
  - `F` is finitely generated;
  - `F` is torsion-free with cyclic centralizers, which gives unique roots and excludes `Z[1/P]` from conjugates
    of `F` in the tree reduction;
  - the single subgroup `φ(F)` meets each cyclic subgroup `⟨s⟩` with index bounded independently of `s`.

  So it applies to ascending HNN extensions of any such `F`.
