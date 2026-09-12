---
rg: 2
id: shared-context-pairwise-antiphase-v4-routing
kind: claim
title: Route repeated V4 failure branches through pair-specific opposite phases
distinct_from:
  shared-context-disjoint-v4-tagging: that must pack all branch labels as disjoint representations of one common finite tag group; this permits a different involution and source word pair for every unordered branch pair.
  repeated-v4-tags-cannot-be-universal-word-branches: that rules out a universally disjoint family of exact branches; this asks for pairwise covariance selected from the shared finite-dimensional packet data and does not assert exact orthogonal branches in the canonical group trace.
---

For the fixed repetition count in `(PAV5)`, construct a finitely presented
marked extension and a decoder for every sufficiently accurate
finite-dimensional marked microstate with the following data.

1. Each repeated V4 radical-atom occurrence has a partial isometry `T_i`
   whose source is that atom and whose target lies in one common fixed matrix
   amplification.
2. For every unordered pair `i<j`, there is a target unitary `R_ij` and
   opposite signs `epsilon_(i,ij)=-epsilon_(j,ij)`.
3. The complete covariance cost satisfies `(PAV3)` with a constant depending
   only on the fixed presentation.
4. Some exact unitary representation retains the central packet sign.  It
   may use properly infinite multiplicity; the non-Connes-embeddable BCS
   trace itself need not extend through the groupifier.

A concrete ordinary-word template is to choose, for each incident pair,
source involution words `w_(i,ij),w_(j,ij)` which act by the two opposite signs
on the corresponding radical atoms, branch transport words `u_i,u_j`, and
impose

```text
u_i w_(i,ij) u_i^(-1)=u_j w_(j,ij) u_j^(-1).          (SCAP1)
```

The common conjugate is the candidate `R_ij`.  Telescoping `(SCAP1)` and the
source-phase defects would give `(PAV3)`.

The hard part is clause 4 together with the source-phase assertions.  A word
whose scalar character singles out an arbitrary nonlinear forbidden atom is
blocked by the affine-selector theorem.  Therefore the source words must use
the nonabelian V4/Schur packet or a finite-dimensional multiplicity decoder,
and their whole tuple at each branch must remain jointly conjugatable on all
satisfying sectors.  Pair-specific words avoid the finite character-packing
ceiling and avoid transitivity through one common tag group, but they do not
by themselves prove this joint completeness condition.

This is the current local construction problem.  A positive solution closes
the fixed-scale V4 return by dimension-free Gram capacity.  A negative result
must rule out pair-specific nonabelian source phases, not merely common affine
tag atlases.

## Attempts

- **One common source involution per branch. Dead.** If the same pair of
  branch labels is reused against every other branch, the obstruction is even
  sharper than stationary tag flow.
  `one-axis-pairwise-antiphase-routing-fails-on-triangles` absorbs the source
  character into that axis and shows that every edge would negate it.  The
  first triangle is inconsistent.  The source word must genuinely depend on
  the incident unordered pair through a multi-axis joint representation.
- **Affine selector characters. Dead for nonlinear failure atoms.** A scalar
  word in the commuting selector subgroup has affine character support and
  cannot distinguish an arbitrary forbidden BCS predicate while remaining
  harmless on every satisfying sector.
- **Independent Clifford axis per incident edge. Dead, sharply.**
  `clifford-radical-antiphase-routing-has-character-capacity` allows a
  different Pauli word on every edge and arbitrary local Clifford frames.  It
  still assigns one effective radical character to each branch, so `N`
  pairwise comparisons require `N<=2^r`.  The V4 law has five failure
  occurrences over its four radical characters.  Dummy radical coordinates
  multiply both numbers equally and preserve the fatal ratio `5/4`.
- **Non-character packet decoder. Active.** The remaining pairwise route must
  use data not reducible to one effective Weyl character per branch: a
  multiplicity-dependent polar decoder, a contextual cross-copy operation,
  or a genuinely non-Weyl coefficient system.  The existing covariant
  Wedderburn detector is the closest proven example of such information, but
  exposing its commutant range by ordinary sparse group relations remains the
  return problem.
- **Pointwise allowed-flat sparse Wedderburn families stop at two types.**
  `support-packet-five-sparse-wedderburn-tag-capacity-is-two` exhausts the
  order-128 packet through five irreducible summands and finds no
  allowed-equivalence class with more than two forbidden commutant types.
  Thus that direct enrichment cannot label the five occurrences.  The live
  route must exploit allowed-source permutations, a larger packet, or an
  operation coupling multiple contextual copies.
