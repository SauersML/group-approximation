---
rg: 2
id: universal-relations-cannot-force-proper-infiniteness
kind: claim
title: No universal group-relation argument can force a properly infinite projection
distinct_from:
  additive-index-instability: that kills additive Fredholm/rank indices by amplification; this kills a different family of shortcuts -- Cuntz pairs, proper isometries and properly infinite projections -- and the mechanism is the canonical trace on the reduced group C*-algebra, not amplification.
  leavitt-unit-group-algebra-not-directly-finite: that is a positive structural fact about the Leavitt group algebra, where a one-sided inverse genuinely exists by construction; this says such a configuration can never be a CONSEQUENCE of group relations alone, so the two never compete.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `G = <S | R>` be a group and let `p` be a projection in `C*_max(G)`
defined by a formula in the group elements -- an averaging idempotent over a
finite subgroup, a Kazhdan projection, or any other element of the group
algebra or its closure specified without reference to a particular
representation. Then the relations `R` **cannot** force `p` to be nonzero and
properly infinite, and in particular cannot force `1` to be properly infinite
or force a proper isometry among the group elements.

Precisely: if every unitary representation of `G` made the image of `p`
nonzero and properly infinite, a contradiction follows.

## Two special cases worth naming

* **Proper isometries among group words are impossible for free.** A group
  word in unitaries is a unitary, so `v^* v = v v^* = 1` in every
  representation, and `||1 - v v^*|| = 1` is unreachable. Any construction
  must therefore go through the closure of the group algebra, which is where
  the trace argument bites.
* **The Kazhdan complement.** For a property `(T)` group `Gamma` that is not
  amenable the Kazhdan projection `p_Gamma` is sent to `0` by the left
  regular representation, so the complement `1 - p_Gamma` is sent to `1`.
  A universal argument forcing `1 - p_Gamma` properly infinite therefore
  forces `1` properly infinite in `C*_r(Gamma)`, and dies the same way.

**Scope.**  This does not say proper infiniteness never occurs in a corona
representation, nor that stable finiteness of the norm matrix corona is
useless. It says the configuration cannot be **derived from the relations
alone**, so a route of the form "these relations force a Cuntz pair, and a
corona is stably finite" is closed before it starts.
