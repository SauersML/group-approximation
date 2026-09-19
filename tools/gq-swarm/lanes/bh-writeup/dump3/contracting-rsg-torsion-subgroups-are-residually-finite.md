---
rg: 2
id: contracting-rsg-torsion-subgroups-are-residually-finite
kind: claim
title: Every finitely generated torsion subgroup of a contracting rational similarity group is residually finite, so the Belk–Bleak–Matucci–Zaremsky hyperbolic hosts contain no infinite group of finite exponent
distinct_from:
  almost-automorphism-torsion-subgroups-are-rf: that proves the statement when every local action is a length-preserving isomorphism of path spaces (almost automorphisms of trees and of finite-graph path spaces, including Röver–Nekrashevych groups); this asks it for contracting RSGs, whose nucleus maps may be asynchronous and non-surjective.
  hyperbolic-groups-satisfy-boone-higman: that embeds hyperbolic groups in finitely presented simple groups built from contracting RSGs; this asks which periodic groups such hosts can contain.
  some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup: that is the existence question for any finitely presented simple group; this would exclude the BBMZ host family from it.
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**OPEN.** Let `G ≤ R_{Γ,E}` be a contracting rational similarity group in the sense of Belk–Bleak–Matucci–Zaremsky
(arXiv:2309.06224, Defs. 2.32 and 2.41). Then every finitely generated torsion subgroup of `G` is residually finite.
So, by Zelmanov (`restricted-burnside-finiteness`), `G` contains no infinite finitely generated group of finite
exponent.

## Why it matters

- **The hosts.** The finitely presented simple hosts of `hyperbolic-groups-satisfy-boone-higman` are built from
  contracting RSGs, so a proof would exclude them as witnesses for
  `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`. This assumes the host is itself a contracting RSG
  (full closure and commutator subgroup), which is not checked here.
- **What is already covered.** Together with `almost-automorphism-torsion-subgroups-are-rf`, the remaining
  Thompson-type Cantor hosts would then be `nV` for `n >= 2` (the questions `brin-thompson-2v-is-torsion-locally-finite`
  and `brin-thompson-groups-contain-infinite-periodic-groups`), twisted Brin–Thompson groups, and finite germ
  extensions.

## Attempts

1. **bh-free-12, 2026-09-18: reduction, tools and the precise obstacle. No proof.**
   - **Case covered.** Suppose every element of the nucleus is a length-preserving bijection `C_v → C_w`. Then each
     `g ∈ G` is an almost automorphism of the path space of `Γ`: finitely many pieces `α ω ↦ β n(ω)`, with the short
     cones as extra pieces. So item 6 of `almost-automorphism-torsion-subgroups-are-rf` (the graph version) applies.
   - **Tool 1: equicontinuity.** A group of homeomorphisms of a Cantor set that is equicontinuous has compact,
     totally disconnected closure in `Homeo`. That closure is profinite, so the group is residually finite. In the
     almost-automorphism proof, Steps 2–3 are exactly a uniform bound making a finitely generated torsion subgroup
     equicontinuous on deep cones.
   - **Tool 2: the clopen trick.** A finite-order homeomorphism `h` with `h(U) ⊆ U` for a clopen `U` has `h(U) = U`.
     So any segment of a trajectory that maps a cone `C_T` into a proper subcone `C_{Ty}` has infinite order. This
     replaces the contraction fixed point of the synchronous proof and needs no length-preservation.
   - **Obstacle A: asynchronous local actions.** BBMZ nucleus elements are injective open maps `C_v → C_w`,
     "not necessarily homeomorphisms" and not length-preserving (arXiv HTML of 2309.06224, Def. 2.5 and the nucleus
     definition, read 2026-09-18). A single rational homeomorphism need not be bi-Lipschitz at small scales. Example:
     `g(0^k 1 w) = 0^(2k) h(1w)`, with `h(10w) = 01w` and `h(11w) = 1w`, is rational and has
     `|ḡ(0^k)| − k = k → ∞`.
     - That `g` is excluded from contracting groups containing `V`: `g^m|_(0^k) = g^m` gives infinitely many
       restrictions.
     - But the per-step depth change is no longer a cocycle, only super-additive:
       `σ(hg, u) >= σ(h, ḡ(u)) + σ(g, u)`.
     - The pumping step also needs the depth increments of a small cone and of the large "top" cone `C_T` to agree
       along a segment. For asynchronous maps they can differ by up to twice the lag per step, and the difference
       accumulates.
   - **Obstacle B: non-surjective local actions.** With non-surjective local actions the image of a deep cone is a
     clopen set rather than a cone. Then even a uniform depth bound does not by itself give finitely many images.
   - **Sharp form of what is needed.** A uniform modulus: there are `D, B` such that for every `h` in the finitely
     generated torsion subgroup and every cone `C_u` with `|u| >= D`, `h(C_u)` is a union of cones of depth at most
     `|u| + B`, contained in a cone of depth at least `|u| − B`. With that, the orbit of each deep cone is finite, `H`
     permutes finitely many clopen sets at each level, and it is residually finite. For asynchronous generators this
     is a nondeterministic pushdown-type pumping statement.
