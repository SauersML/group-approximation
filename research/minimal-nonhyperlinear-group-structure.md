---
rg: 2
id: minimal-nonhyperlinear-group-structure
kind: claim
title: A minimal nonhyperlinear group is finitely generated, perfect, without finite quotients or amenable-edge splittings, and maps onto a nonamenable simple group
distinct_from:
  nonhyperlinear-existence-is-two-generator-simple: that embeds a nonhyperlinear group into a simple overgroup; this constrains a group whose proper subgroups are all hyperlinear, and finds a simple quotient with hyperlinear kernel inside it.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that is the permanence theorem for amenable-edge graphs of groups; this applies it to force a minimal nonhyperlinear group to coincide with one vertex group of any such splitting.
  amenable-quotient-preserves-metric-approximability: that is the extension permanence theorem; this applies it to show a minimal nonhyperlinear group has no proper normal subgroup with amenable quotient.
  mf-nonhyperlinear-residual-with-amenable-quotient-is-critical: that produces groups with no nontrivial hyperlinear quotient (minimality among quotients); this is minimality among subgroups, and neither property implies the other.
artifacts:
  - research/artifacts/lcs-five-equations-and-minimal-nonhyperlinear-2026-09-16.md
---

ESTABLISHED (2026-09-16), by `minimal-nonhyperlinear-group-structure-proof`,
from three ESTABLISHED permanence nodes.

## Definition

A group `G` is **minimal nonhyperlinear** (MNH) if `G` is not hyperlinear and
every proper subgroup of `G` is hyperlinear. This is the hyperlinear form of
Ersoy's minimal non-sofic groups (arXiv:2604.19174, Definition 1.3; Remark 2.8
mentions the hyperlinear version and leaves it aside).

## Theorem MNH

Let `G` be minimal nonhyperlinear.

- **(M1)** `G` is finitely generated, infinite and nonamenable.
- **(M2)** If `N` is normal in `G` and `G/N` is amenable, then `N = G`. So `G`
  is perfect, has no proper subgroup of finite index, and has no nontrivial
  amenable quotient.
- **(M3)** Every homomorphism from `G` to a residually finite group is trivial.
- **(M4)** Let `G = pi_1(Gcal)` for a finite connected graph of groups with
  injective edge maps and amenable edge groups. Then some vertex group `G_v` is
  nonhyperlinear, and the canonical image of `G_v` in `G` is all of `G`.
- **(M5)** `G` has maximal normal subgroups. For each maximal normal subgroup
  `M`, `M` is hyperlinear and `G/M` is a finitely generated, infinite,
  nonamenable simple group.
- **(M6)** *(existence dichotomy)* Every nonhyperlinear group either contains
  an MNH subgroup, or contains a strictly descending chain of finitely
  generated nonhyperlinear subgroups.

The second half of (M4) uses injectivity of the canonical maps
`G_v -> pi_1(Gcal)`, which is standard Bass--Serre theory (Serre, *Trees*,
Ch. I §5; cited, not fetched). The node
`amenable-edge-graph-corners-cannot-groupify-a-nonce-game` presupposes the same
theory.

## Why it is true (sketch)

- **(M1)** Locality gives a finitely generated nonhyperlinear subgroup, which
  must be all of `G`. Amenable groups are hyperlinear.
- **(M2)** A proper normal `N` is hyperlinear. If `G/N` were amenable, the
  extension theorem would make `G` hyperlinear.
- **(M3)** A nontrivial map to a residually finite group gives a proper normal
  subgroup of finite index.
- **(M4)** If all vertex groups were hyperlinear, so would `G` be.
- **(M5)** Finite generation plus Zorn's lemma gives a maximal normal subgroup,
  and (M2) makes the simple quotient nonamenable.
- **(M6)** Dependent choice.

## Consequences resting on classical theorems

These are remarks, not part of the established content. Each imports a
classical theorem that was not re-fetched.
- **Malcev.** An MNH group has no nontrivial finite-dimensional linear
  representation.
- **Baumslag.** A finitely generated residually finite normal subgroup of an
  MNH group is central. If a maximal normal subgroup has these properties, then
  `G` is a perfect central extension of a nonamenable simple group, the
  hyperlinear analogue of Ersoy's sofic theorem.
- **Stallings.** An MNH group is one-ended. It admits no nontrivial free
  product, amalgam or HNN decomposition over an amenable subgroup.

## Where it stops

The theorem constrains a hypothetical MNH group and constructs none. Existence
of an MNH group is not known to follow from existence of a nonhyperlinear
group: a descending chain as in (M6) can intersect in a hyperlinear group, so
Zorn's lemma does not apply. The simple quotient in (M5) need not be
nonhyperlinear, because there is no permanence theorem for a hyperlinear
kernel with a nonamenable quotient.
